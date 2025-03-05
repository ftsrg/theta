/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.cli.params

import com.beust.jcommander.Parameter
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker.IterationStrategy
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.chc.ChcFrontend
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.oc.AutoConflictFinderConfig
import hu.bme.mit.theta.xcfa.analysis.oc.OcDecisionProcedureType
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.LbePass
import java.io.File
import java.nio.file.Paths

interface Config {

  fun getObjects(): Set<Config> = setOf(this)

  fun update(): Boolean = false
}

interface SpecializableConfig<T : Config> : Config {

  val specConfig: T?

  override fun getObjects(): Set<Config> = setOf(this) union (specConfig?.getObjects() ?: setOf())

  fun createSpecConfig()

  override fun update(): Boolean =
    specConfig?.update() ?: createSpecConfig().let { specConfig != null }
}

data class XcfaConfig<F : SpecFrontendConfig, B : SpecBackendConfig>(
  val inputConfig: InputConfig = InputConfig(),
  val frontendConfig: FrontendConfig<F> = FrontendConfig(),
  val backendConfig: BackendConfig<B> = BackendConfig(),
  val outputConfig: OutputConfig = OutputConfig(),
  val debugConfig: DebugConfig = DebugConfig(),
) : Config {

  override fun getObjects(): Set<Config> {
    return inputConfig.getObjects() union
      frontendConfig.getObjects() union
      backendConfig.getObjects() union
      outputConfig.getObjects() union
      debugConfig.getObjects()
  }

  override fun update(): Boolean =
    listOf(inputConfig, frontendConfig, backendConfig, outputConfig, debugConfig)
      .map { it.update() }
      .any { it == true }
}

data class InputConfig(
  @Parameter(names = ["--input"], description = "Path of the input model") var input: File? = null,
  @Parameter(names = ["--cat"], description = "Path of the cat model") var catFile: File? = null,
  @Parameter(
    names = ["--parse-ctx"],
    description = "Path of the parse context JSON (may contain additional metadata)",
  )
  var parseCtx: File? = null,
  @Parameter(
    names = ["--xcfa-w-ctx"],
    description = "XCFA and ParseContext (will overwrite --input and --parse-ctx when given)",
  )
  var xcfaWCtx: Triple<XCFA, MCM, ParseContext>? = null,
  @Parameter(
    names = ["--property"],
    description = "Path of the property file (will overwrite --property when given)",
  )
  var propertyFile: File? = null,
  @Parameter(names = ["--property-value"], description = "Property")
  var property: ErrorDetection = ErrorDetection.ERROR_LOCATION,
) : Config {

  override fun toString(): String {
    return "InputConfig(inputFile=${input}, catFile=${catFile}, parseCtx=${parseCtx}, " +
      "xcfaWCtx=${xcfaWCtx?.let { "present" } ?: "missing"}, propertyFile=${propertyFile}, property=${property}"
  }
}

interface SpecFrontendConfig : Config

data class FrontendConfig<T : SpecFrontendConfig>(
  @Parameter(names = ["--lbe"], description = "Level of LBE (NO_LBE, LBE_LOCAL, LBE_SEQ, LBE_FULL)")
  var lbeLevel: LbePass.LbeLevel = LbePass.LbeLevel.LBE_SEQ,
  @Parameter(names = ["--static-coi"], description = "Enable static cone-of-influence")
  var staticCoi: Boolean = false,
  @Parameter(
    names = ["--unroll"],
    description =
      "Max number of loop iterations to unroll (use -1 to unroll completely when possible)",
  )
  var loopUnroll: Int = 1000,
  @Parameter(
    names = ["--force-unroll"],
    description =
      "Number of loop iteration to unroll even if the number of iterations is unknown; in case of such a bounded loop unrolling, the safety result cannot be safe (use -1 to disable)",
  )
  var forceUnroll: Int = -1,
  @Parameter(
    names = ["--enable-few"],
    description =
      "Enable the FetchExecuteWriteback pass, which introduces a local temp var for all memory accesses",
  )
  var enableFew: Boolean = false,
  @Parameter(names = ["--input-type"], description = "Format of the input")
  var inputType: InputType = InputType.C,
  override var specConfig: T? = null,
) : SpecializableConfig<T> {

  override fun createSpecConfig() {
    specConfig =
      when (inputType) {
        InputType.C -> CFrontendConfig() as T
        InputType.LLVM -> null
        InputType.JSON -> null
        InputType.DSL -> null
        InputType.LITMUS -> null
        InputType.CFA -> null
        InputType.CHC -> CHCFrontendConfig() as T
      }
  }
}

data class CFrontendConfig(
  @Parameter(
    names = ["--arithmetic"],
    description = "Arithmetic type (efficient, bitvector, integer)",
  )
  var arithmetic: ArchitectureConfig.ArithmeticType = ArchitectureConfig.ArithmeticType.efficient,
  @Parameter(
    names = ["--architecture"],
    description = "Architecture (see https://unix.org/whitepapers/64bit.html)",
  )
  var architecture: ArchitectureConfig.ArchitectureType = ArchitectureConfig.ArchitectureType.LP64,
) : SpecFrontendConfig

data class CHCFrontendConfig(
  @Parameter(
    names = ["--chc-transformation"],
    description = "Direction of transformation from CHC to XCFA",
  )
  var chcTransformation: ChcFrontend.ChcTransformation = ChcFrontend.ChcTransformation.PORTFOLIO
) : SpecFrontendConfig

interface SpecBackendConfig : Config

data class BackendConfig<T : SpecBackendConfig>(
  @Parameter(names = ["--backend"], description = "Backend analysis to use")
  var backend: Backend = Backend.CEGAR,
  @Parameter(names = ["--smt-home"], description = "The path of the solver registry")
  var solverHome: String = SmtLibSolverManager.HOME.toAbsolutePath().toString(),
  @Parameter(
    names = ["--timeout-ms"],
    description = "Timeout for verification, use 0 for no timeout",
  )
  var timeoutMs: Long = 0,
  @Parameter(names = ["--in-process"], description = "Run analysis in process")
  var inProcess: Boolean = false,
  @Parameter(
    names = ["--memlimit"],
    description = "Maximum memory to use when --in-process (in bytes, 0 for default)",
  )
  var memlimit: Long = 0L,
  override var specConfig: T? = null,
) : SpecializableConfig<T> {

  override fun createSpecConfig() {
    specConfig =
      when (backend) {
        Backend.CEGAR -> CegarConfig() as T
        Backend.BOUNDED -> BoundedConfig() as T
        Backend.CHC -> HornConfig() as T
        Backend.OC -> OcConfig() as T
        Backend.LAZY -> null
        Backend.PORTFOLIO -> PortfolioConfig() as T
        Backend.MDD -> MddConfig() as T
        Backend.LASSO_VALIDATION -> LassoValidationConfig() as T
        Backend.NONE -> null
        Backend.IC3 -> Ic3Config() as T
      }
  }
}

data class CegarConfig(
  @Parameter(names = ["--initprec"], description = "Initial precision")
  var initPrec: InitPrec = InitPrec.EMPTY,
  @Parameter(names = ["--por-level"], description = "POR dependency level")
  var porLevel: POR = POR.NOPOR,
  @Parameter(names = ["--por-seed"], description = "Random seed used for DPOR")
  var porRandomSeed: Int = -1,
  @Parameter(names = ["--coi"], description = "Enable ConeOfInfluence")
  var coi: ConeOfInfluenceMode = ConeOfInfluenceMode.NO_COI,
  @Parameter(
    names = ["--cex-monitor"],
    description = "Option to enable(CHECK)/disable(DISABLE) the CexMonitor",
  )
  var cexMonitor: CexMonitorOptions = CexMonitorOptions.CHECK,
  val abstractorConfig: CegarAbstractorConfig = CegarAbstractorConfig(),
  val refinerConfig: CegarRefinerConfig = CegarRefinerConfig(),
) : SpecBackendConfig {

  override fun getObjects(): Set<Config> {
    return super.getObjects() union abstractorConfig.getObjects() union refinerConfig.getObjects()
  }

  override fun update(): Boolean =
    listOf(abstractorConfig, refinerConfig).map { it.update() }.any { it }
}

data class CegarAbstractorConfig(
  @Parameter(names = ["--abstraction-solver"], description = "Abstraction solver name")
  var abstractionSolver: String = "Z3",
  @Parameter(
    names = ["--validate-abstraction-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateAbstractionSolver: Boolean = false,
  @Parameter(names = ["--domain"], description = "Abstraction domain")
  var domain: Domain = Domain.EXPL,
  @Parameter(
    names = ["--maxenum"],
    description =
      "How many successors to enumerate in a transition. Only relevant to the explicit domain. Use 0 for no limit.",
  )
  var maxEnum: Int = 1,
  @Parameter(names = ["--search"], description = "Search strategy") var search: Search = Search.ERR,
  @Parameter(
    names = ["--havoc-memory"],
    description = "HAVOC memory model (do not track pointers in transition function)",
  )
  var havocMemory: Boolean = false,
) : Config

data class CegarRefinerConfig(
  @Parameter(names = ["--refinement-solver"], description = "Refinement solver name")
  var refinementSolver: String = "Z3",
  @Parameter(
    names = ["--validate-refinement-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateRefinementSolver: Boolean = false,
  @Parameter(names = ["--refinement"], description = "Refinement strategy")
  var refinement: Refinement = Refinement.SEQ_ITP,
  @Parameter(
    names = ["--predsplit"],
    description = "Predicate splitting (for predicate abstraction)",
  )
  var exprSplitter: ExprSplitterOptions = ExprSplitterOptions.WHOLE,
  @Parameter(
    names = ["--prunestrategy"],
    description = "Strategy for pruning the ARG after refinement",
  )
  var pruneStrategy: PruneStrategy = PruneStrategy.LAZY,
) : Config

data class HornConfig(
  @Parameter(names = ["--solver"], description = "Solver to use.") var solver: String = "Z3:4.13",
  @Parameter(
    names = ["--validate-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateSolver: Boolean = false,
) : SpecBackendConfig

data class LassoValidationConfig(
  @Parameter(names = ["--solver"], description = "Solver to use.") var solver: String = "Z3:4.13",
  @Parameter(
    names = ["--validate-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateSolver: Boolean = false,
  @Parameter(names = ["--witness"], description = "Path of the witness file (witness.yml)")
  var witness: File? = null,
) : SpecBackendConfig

data class BoundedConfig(
  @Parameter(names = ["--max-bound"], description = "Maximum bound to check. Use 0 for no limit.")
  var maxBound: Int = 0,
  @Parameter(names = ["--reversed"], description = "Create a reversed monolithic expression")
  var reversed: Boolean = false,
  @Parameter(names = ["--cegar"], description = "Wrap the check in a predicate-based CEGAR loop")
  var cegar: Boolean = false,
  @Parameter(names = ["--initprec"], description = "Wrap the check in a predicate-based CEGAR loop")
  var initPrec: InitPrec = InitPrec.EMPTY,
  val bmcConfig: BMCConfig = BMCConfig(),
  val indConfig: InductionConfig = InductionConfig(),
  val itpConfig: InterpolationConfig = InterpolationConfig(),
) : SpecBackendConfig {

  override fun getObjects(): Set<Config> {
    return super.getObjects() union
      bmcConfig.getObjects() union
      indConfig.getObjects() union
      itpConfig.getObjects()
  }

  override fun update(): Boolean =
    listOf(bmcConfig, indConfig, itpConfig).map { it.update() }.any { it }
}

data class BMCConfig(
  @Parameter(names = ["--no-bmc"], description = "Disable SAT check") var disable: Boolean = false,
  @Parameter(names = ["--non-lf-path"], description = "Disable loop-freeness check")
  var nonLfPath: Boolean = false,
  @Parameter(names = ["--bmc-solver"], description = "BMC solver name")
  var bmcSolver: String = "Z3",
  @Parameter(
    names = ["--validate-bmc-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateBMCSolver: Boolean = false,
) : Config

data class InductionConfig(
  @Parameter(names = ["--no-induction"], description = "Disable induction check")
  var disable: Boolean = false,
  @Parameter(names = ["--induction-solver", "--ind-solver"], description = "Induction solver name")
  var indSolver: String = "Z3",
  @Parameter(
    names = ["--validate-induction-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateIndSolver: Boolean = false,
  @Parameter(names = ["--ind-min-bound"], description = "Start induction after reaching this bound")
  var indMinBound: Int = 0,
  @Parameter(names = ["--ind-frequency"], description = "Frequency of induction check")
  var indFreq: Int = 1,
) : Config

data class InterpolationConfig(
  @Parameter(names = ["--no-interpolation"], description = "Disable interpolation check")
  var disable: Boolean = false,
  @Parameter(
    names = ["--interpolation-solver", "--itp-solver"],
    description = "Interpolation solver name",
  )
  var itpSolver: String = "Z3",
  @Parameter(
    names = ["--validate-interpolation-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateItpSolver: Boolean = false,
) : Config

data class OcConfig(
  @Parameter(
    names = ["--oc-decision-procedure"],
    description = "Decision procedure for ordering-consistency check",
  )
  var decisionProcedure: OcDecisionProcedureType = OcDecisionProcedureType.PROPAGATOR,
  @Parameter(names = ["--input-conflicts"], description = "Input file containing conflict clauses")
  var inputConflictClauseFile: String? = null,
  @Parameter(names = ["--output-conflicts"], description = "Enables conflict clause logging")
  var outputConflictClauses: Boolean = false,
  @Parameter(
    names = ["--input-conflict-decision-procedure"],
    description = "Output file to write conflict clauses",
  )
  var inputConflictDecisionProcedure: String = "",
  @Parameter(
    names = ["--non-permissive-validation"],
    description = "Output file to write conflict clauses",
  )
  var nonPermissiveValidation: Boolean = false,
  @Parameter(
    names = ["--auto-conflict"],
    description = "Level of manual conflict detection before verification",
  )
  var autoConflict: AutoConflictFinderConfig = AutoConflictFinderConfig.NONE,
) : SpecBackendConfig

data class PortfolioConfig(
  @Parameter(names = ["--portfolio"], description = "Portfolio to run")
  var portfolio: String = "COMPLEX"
) : SpecBackendConfig

data class MddConfig(
  @Parameter(names = ["--solver", "--mdd-solver"], description = "MDD solver name")
  var solver: String = "Z3",
  @Parameter(
    names = ["--validate-solver", "--validate-mdd-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateSolver: Boolean = false,
  @Parameter(
    names = ["--iteration-strategy"],
    description = "Iteration strategy for the MDD checker",
  )
  var iterationStrategy: IterationStrategy = IterationStrategy.GSAT,
  @Parameter(names = ["--reversed"], description = "Create a reversed monolithic expression")
  var reversed: Boolean = false,
  @Parameter(names = ["--cegar"], description = "Wrap the check in a predicate-based CEGAR loop")
  var cegar: Boolean = false,
  @Parameter(names = ["--initprec"], description = "Wrap the check in a predicate-based CEGAR loop")
  var initPrec: InitPrec = InitPrec.EMPTY,
) : SpecBackendConfig

data class Ic3Config(
  @Parameter(names = ["--solver", "--mdd-solver"], description = "MDD solver name")
  var solver: String = "Z3",
  @Parameter(
    names = ["--validate-solver", "--validate-mdd-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateSolver: Boolean = false,
  @Parameter(names = ["--reversed"], description = "Create a reversed monolithic expression")
  var reversed: Boolean = false,
  @Parameter(names = ["--cegar"], description = "Wrap the check in a predicate-based CEGAR loop")
  var cegar: Boolean = false,
  @Parameter(names = ["--initprec"], description = "Wrap the check in a predicate-based CEGAR loop")
  var initPrec: InitPrec = InitPrec.EMPTY,
) : SpecBackendConfig

data class OutputConfig(
  @Parameter(names = ["--version"], description = "Display version", help = true)
  var versionInfo: Boolean = false,
  @Parameter(names = ["--enable-output"], description = "Enable output files")
  var enableOutput: Boolean = false,
  @Parameter(
    names = ["--output-directory"],
    description = "Specify the directory where the result files are stored",
  )
  var resultFolder: File = Paths.get("./").toFile(),
  @Parameter(
    names = ["--accept-unreliable-safe"],
    description = "Accept safe results even with unsafe loop unroll",
  )
  var acceptUnreliableSafe: Boolean = false,
  val cOutputConfig: COutputConfig = COutputConfig(),
  val xcfaOutputConfig: XcfaOutputConfig = XcfaOutputConfig(),
  val chcOutputConfig: ChcOutputConfig = ChcOutputConfig(),
  val witnessConfig: WitnessConfig = WitnessConfig(),
  val argConfig: ArgConfig = ArgConfig(),
) : Config {

  override fun getObjects(): Set<Config> {
    return super.getObjects() union
      cOutputConfig.getObjects() union
      xcfaOutputConfig.getObjects() union
      chcOutputConfig.getObjects() union
      witnessConfig.getObjects() union
      argConfig.getObjects()
  }

  override fun update(): Boolean =
    listOf(cOutputConfig, xcfaOutputConfig, chcOutputConfig, witnessConfig, argConfig)
      .map { it.update() }
      .any { it }
}

data class XcfaOutputConfig(
  @Parameter(names = ["--disable-xcfa-serialization"]) var disable: Boolean = false
) : Config

data class ChcOutputConfig(
  @Parameter(names = ["--disable-chc-serialization"]) var disable: Boolean = false
) : Config

data class COutputConfig(
  @Parameter(names = ["--disable-c-serialization"]) var disable: Boolean = false,
  @Parameter(names = ["--to-c-use-arrays"]) var useArr: Boolean = false,
  @Parameter(names = ["--to-c-use-exact-arrays"]) var useExArr: Boolean = false,
  @Parameter(names = ["--to-c-use-ranges"]) var useRange: Boolean = false,
) : Config

data class WitnessConfig(
  @Parameter(names = ["--disable-witness-generation"]) var disable: Boolean = false,
  @Parameter(names = ["--only-svcomp-witness"]) var svcomp: Boolean = false,
  @Parameter(names = ["--cex-solver"], description = "Concretizer solver name")
  var concretizerSolver: String = "Z3",
  @Parameter(
    names = ["--validate-cex-solver"],
    description =
      "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.",
  )
  var validateConcretizerSolver: Boolean = false,
  @Parameter(names = ["--input-file-for-witness"]) var inputFileForWitness: File? = null,
) : Config

data class ArgConfig(
  @Parameter(names = ["--disable-arg-generation"]) var disable: Boolean = false
) : Config

data class DebugConfig(
  @Parameter(
    names = ["--debug"],
    description = "Debug mode (not exiting when encountering an exception)",
  )
  var debug: Boolean = false,
  @Parameter(names = ["--stacktrace"], description = "Print full stack trace in case of exception")
  var stacktrace: Boolean = false,
  @Parameter(names = ["--loglevel"], description = "Detailedness of logging")
  var logLevel: Logger.Level = Logger.Level.MAINSTEP,
  @Parameter(
    names = ["--arg-debug"],
    description = "ARG debug mode (use the web-based debugger for ARG visualization)",
  )
  var argdebug: Boolean = false,
  @Parameter(
    names = ["--arg-to-file"],
    description =
      "Visualize the resulting file here: https://ftsrg-edu.github.io/student-sisak-argviz/",
  )
  var argToFile: Boolean = false,
) : Config
