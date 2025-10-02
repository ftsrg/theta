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
package hu.bme.mit.theta.xcfa.cli.portfolio

import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.LoopUnrollPass

fun boundedPortfolio25(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  var boundedBaseConfig =
    XcfaConfig(
      inputConfig =
        InputConfig(
          input = null,
          xcfaWCtx = Triple(xcfa, mcm, parseContext),
          propertyFile = null,
          property = portfolioConfig.inputConfig.property,
        ),
      frontendConfig =
        FrontendConfig(
          lbeLevel = LbePass.level,
          loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
          inputType = InputType.C,
          specConfig = CFrontendConfig(arithmetic = ArchitectureConfig.ArithmeticType.efficient),
        ),
      backendConfig =
        BackendConfig(
          backend = Backend.BOUNDED,
          memlimit = portfolioConfig.backendConfig.memlimit,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          specConfig =
            BoundedConfig(
              bmcConfig = BMCConfig(true),
              maxBound = 0,
              indConfig = InductionConfig(true),
              itpConfig = InterpolationConfig(true),
            ),
        ),
      outputConfig =
        OutputConfig(
          versionInfo = false,
          resultFolder = portfolioConfig.outputConfig.resultFolder, // cwd
          cOutputConfig = COutputConfig(disable = true),
          witnessConfig =
            WitnessConfig(
              disable = false,
              concretizerSolver = "Z3",
              validateConcretizerSolver = false,
              inputFileForWitness =
                portfolioConfig.outputConfig.witnessConfig.inputFileForWitness
                  ?: portfolioConfig.inputConfig.input,
            ),
          argConfig = ArgConfig(disable = true),
          enableOutput = portfolioConfig.outputConfig.enableOutput,
        ),
      debugConfig = portfolioConfig.debugConfig,
    )

  val mddBaseConfig =
    XcfaConfig(
      inputConfig = boundedBaseConfig.inputConfig,
      frontendConfig = boundedBaseConfig.frontendConfig,
      backendConfig =
        BackendConfig(
          backend = Backend.MDD,
          memlimit = portfolioConfig.backendConfig.memlimit / 5 * 4,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          specConfig =
            MddConfig(
              solver = "Z3",
              validateSolver = false,
              iterationStrategy = MddChecker.IterationStrategy.GSAT,
              reversed = false,
              cegar = false,
              initPrec = InitPrec.EMPTY,
            ),
        ),
      outputConfig = boundedBaseConfig.outputConfig,
      debugConfig = boundedBaseConfig.debugConfig,
    )

  if (parseContext.multiThreading) {
    throw UnsupportedOperationException("Multithreading for bounded checkers not supported")
  }

  if (!xcfa.isInlined) {
    throw UnsupportedOperationException("Recursive XCFA for bounded checkers not supported")
  }

  val timeoutOrNotSolvableError =
    ExceptionTrigger(
      fallthroughExceptions =
        setOf(
          ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
          ErrorCodeException(ExitCodes.SERVER_ERROR.code),
        ),
      label = "TimeoutOrNotSolvableError",
    )

  val timeoutOrSolverError =
    ExceptionTrigger(
      fallthroughExceptions = setOf(ErrorCodeException(ExitCodes.SERVER_ERROR.code)),
      label = "TimeoutOrSolverError",
    )

  val solverError =
    ExceptionTrigger(ErrorCodeException(ExitCodes.SOLVER_ERROR.code), label = "SolverError")

  val anyError = ExceptionTrigger(label = "Anything")

  fun XcfaConfig<CFrontendConfig, BoundedConfig>.adaptConfig(
    bmcEnabled: Boolean = false,
    indEnabled: Boolean = false,
    itpEnabled: Boolean = false,
    bmcSolver: String = "Z3",
    indSolver: String = "Z3",
    itpSolver: String = "cvc5:1.0.8",
    timeoutMs: Long = 0,
    inProcess: Boolean = this.backendConfig.inProcess,
    reversed: Boolean = false,
    cegar: Boolean = false,
    initprec: InitPrec = InitPrec.EMPTY,
  ): XcfaConfig<*, BoundedConfig> {
    return copy(
      backendConfig =
        backendConfig.copy(
          timeoutMs = timeoutMs,
          inProcess = inProcess,
          specConfig =
            backendConfig.specConfig!!.copy(
              reversed = reversed,
              cegar = cegar,
              initPrec = initprec,
              bmcConfig =
                backendConfig.specConfig!!
                  .bmcConfig
                  .copy(disable = !bmcEnabled, bmcSolver = bmcSolver),
              indConfig =
                backendConfig.specConfig!!
                  .indConfig
                  .copy(disable = !indEnabled, indSolver = indSolver),
              itpConfig =
                backendConfig.specConfig!!
                  .itpConfig
                  .copy(disable = !itpEnabled, itpSolver = itpSolver),
            ),
        )
    )
  }

  fun XcfaConfig<CFrontendConfig, MddConfig>.adaptConfig(
    timeoutMs: Long = 0,
    inProcess: Boolean = this.backendConfig.inProcess,
  ): XcfaConfig<*, MddConfig> {
    return copy(backendConfig = backendConfig.copy(timeoutMs = timeoutMs, inProcess = inProcess))
  }

  val canUseMathsat = !parseContext.arithmeticTraits.contains(ArithmeticTrait.FLOAT)

  fun getMddConfig(inProcess: Boolean): Node =
    ConfigNode(
      "MddZ3-GSAT-$inProcess",
      mddBaseConfig.adaptConfig(inProcess = inProcess, timeoutMs = 180_000),
      checker,
    )

  fun getBmcConfig(inProcess: Boolean): Node {
    val edges = LinkedHashSet<Edge>()
    lateinit var lastNode: ConfigNode

    val configBmcZ3 =
      ConfigNode(
        "BmcZ3-$inProcess",
        boundedBaseConfig.adaptConfig(inProcess = inProcess, bmcEnabled = true, timeoutMs = 30_000),
        checker,
      )
    lastNode = configBmcZ3
    if (canUseMathsat) {
      val configBmcMathsat =
        ConfigNode(
          "BmcMathsat-$inProcess",
          boundedBaseConfig.adaptConfig(
            inProcess = inProcess,
            bmcSolver = "mathsat:5.6.10",
            bmcEnabled = true,
            timeoutMs = 30_000,
          ),
          checker,
        )
      edges.add(Edge(lastNode, configBmcMathsat, solverError))
      lastNode = configBmcMathsat
    }
    val configBmcCvc5 =
      ConfigNode(
        "BmcCvc5-$inProcess",
        boundedBaseConfig.adaptConfig(
          inProcess = inProcess,
          bmcSolver = "cvc5:1.0.8",
          bmcEnabled = true,
          timeoutMs = 30_000,
        ),
        checker,
      )
    edges.add(Edge(lastNode, configBmcCvc5, solverError))
    lastNode = configBmcCvc5

    return HierarchicalNode("BMC_$inProcess", STM(configBmcZ3, edges))
  }

  fun getKindConfig(inProcess: Boolean): Node {
    val edges = LinkedHashSet<Edge>()
    lateinit var lastNode: ConfigNode

    val configKindZ3 =
      ConfigNode(
        "KindZ3-$inProcess",
        boundedBaseConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = true,
          timeoutMs = 300_000,
        ),
        checker,
      )
    lastNode = configKindZ3

    val configKindCvc5 =
      ConfigNode(
        "KindCvc5-$inProcess",
        boundedBaseConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = true,
          bmcSolver = "cvc5:1.0.8",
          indSolver = "cvc5:1.0.8",
          timeoutMs = 300_000,
        ),
        checker,
      )
    edges.add(Edge(lastNode, configKindCvc5, solverError))
    lastNode = configKindCvc5

    if (canUseMathsat) {
      val configKindMathsat =
        ConfigNode(
          "KindMathsat-$inProcess",
          boundedBaseConfig.adaptConfig(
            inProcess = inProcess,
            bmcEnabled = true,
            indEnabled = true,
            bmcSolver = "mathsat:5.6.10",
            indSolver = "mathsat:5.6.10",
            timeoutMs = 300_000,
          ),
          checker,
        )
      edges.add(Edge(lastNode, configKindMathsat, solverError))
      lastNode = configKindMathsat
    }

    return HierarchicalNode("KIND_$inProcess", STM(configKindZ3, edges))
  }

  fun getIMCConfig(inProcess: Boolean): Node {
    val edges = LinkedHashSet<Edge>()
    lateinit var lastNode: ConfigNode

    val configIMCZ3abstract =
      ConfigNode(
        "IMCZ3-abstract-$inProcess",
        boundedBaseConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = true,
          cegar = true,
          timeoutMs = 300_000,
        ),
        checker,
      )
    lastNode = configIMCZ3abstract

    val configRIMCZ3 =
      ConfigNode(
        "RIMCZ3-$inProcess",
        boundedBaseConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = true,
          reversed = true,
          timeoutMs = 300_000,
        ),
        checker,
      )
    edges.add(Edge(lastNode, configRIMCZ3, solverError))
    lastNode = configRIMCZ3

    val configRIMCCvc5 =
      ConfigNode(
        "RIMCCvc5-$inProcess",
        boundedBaseConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = true,
          reversed = true,
          bmcSolver = "cvc5:1.0.8",
          indSolver = "cvc5:1.0.8",
          timeoutMs = 300_000,
        ),
        checker,
      )
    edges.add(Edge(lastNode, configRIMCCvc5, solverError))
    lastNode = configRIMCCvc5

    if (canUseMathsat) {
      val configRIMCMathsat =
        ConfigNode(
          "RIMCMathsat-$inProcess",
          boundedBaseConfig.adaptConfig(
            inProcess = inProcess,
            bmcEnabled = true,
            indEnabled = true,
            reversed = true,
            bmcSolver = "mathsat:5.6.10",
            indSolver = "mathsat:5.6.10",
            timeoutMs = 300_000,
          ),
          checker,
        )
      edges.add(Edge(lastNode, configRIMCMathsat, solverError))
      lastNode = configRIMCMathsat
    }

    return HierarchicalNode("IMC_$inProcess", STM(configIMCZ3abstract, edges))
  }

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    val mddConfig = getMddConfig(inProcess)
    val bmcConfig = getBmcConfig(inProcess)
    val indConfig = getKindConfig(inProcess)
    val imcConfig = getIMCConfig(inProcess)

    edges.add(Edge(mddConfig, bmcConfig, if (inProcess) timeoutOrNotSolvableError else anyError))
    edges.add(Edge(bmcConfig, indConfig, if (inProcess) timeoutOrNotSolvableError else anyError))
    edges.add(Edge(indConfig, imcConfig, if (inProcess) timeoutOrNotSolvableError else anyError))

    return if (inProcess) STM(mddConfig, edges)
    else STM(bmcConfig, edges) // mdd should not be run not-in-proc
  }

  logger.write(Logger.Level.RESULT, "Using bounded portfolio\n")

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
