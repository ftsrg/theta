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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.LoopUnrollPass
import java.nio.file.Paths

fun boundedPortfolio24(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  var baseConfig =
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
          resultFolder = Paths.get("./").toFile(), // cwd
          cOutputConfig = COutputConfig(disable = true),
          witnessConfig =
            WitnessConfig(
              disable = false,
              concretizerSolver = "Z3",
              validateConcretizerSolver = false,
            ),
          argConfig = ArgConfig(disable = true),
          enableOutput = portfolioConfig.outputConfig.enableOutput,
        ),
      debugConfig = portfolioConfig.debugConfig,
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

  fun XcfaConfig<*, BoundedConfig>.adaptConfig(
    bmcEnabled: Boolean = false,
    indEnabled: Boolean = false,
    itpEnabled: Boolean = false,
    bmcSolver: String = "Z3",
    indSolver: String = "Z3",
    itpSolver: String = "cvc5:1.0.8",
    timeoutMs: Long = 0,
    inProcess: Boolean = this.backendConfig.inProcess,
  ): XcfaConfig<*, BoundedConfig> {
    return copy(
      backendConfig =
        backendConfig.copy(
          timeoutMs = timeoutMs,
          inProcess = inProcess,
          specConfig =
            backendConfig.specConfig!!.copy(
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

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()
    val configBmcZ3 =
      ConfigNode(
        "BmcZ3-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, bmcEnabled = true, timeoutMs = 30000),
        checker,
      )
    val configBmcMathsat =
      ConfigNode(
        "BmcMathsat-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          bmcSolver = "mathsat:5.6.10",
          bmcEnabled = true,
          timeoutMs = 30000,
        ),
        checker,
      )
    val configIndZ3 =
      ConfigNode(
        "IndZ3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = true,
          timeoutMs = 300000,
        ),
        checker,
      )
    val configIndMathsat =
      ConfigNode(
        "IndMathsat-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          bmcSolver = "mathsat:5.6.10",
          indSolver = "mathsat:5.6.10",
          bmcEnabled = true,
          indEnabled = true,
          timeoutMs = 300000,
        ),
        checker,
      )
    val configItpCvc5 =
      ConfigNode(
        "ItpCvc5-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          itpEnabled = true,
          itpSolver = "cvc5:1.0.8",
          timeoutMs = 0,
        ),
        checker,
      )
    val configItpMathsat =
      ConfigNode(
        "ItpMathsat-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          itpSolver = "mathsat:5.6.10",
          itpEnabled = true,
          timeoutMs = 0,
        ),
        checker,
      )

    edges.add(Edge(configBmcZ3, configBmcMathsat, solverError))
    edges.add(
      Edge(configBmcZ3, configIndZ3, if (inProcess) timeoutOrNotSolvableError else anyError)
    )
    edges.add(
      Edge(
        configBmcMathsat,
        configIndMathsat,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )

    edges.add(Edge(configIndZ3, configIndMathsat, solverError))
    edges.add(
      Edge(configIndZ3, configItpCvc5, if (inProcess) timeoutOrNotSolvableError else anyError)
    )
    edges.add(
      Edge(configIndMathsat, configItpCvc5, if (inProcess) timeoutOrNotSolvableError else anyError)
    )

    edges.add(Edge(configItpCvc5, configItpMathsat, anyError))

    return STM(configBmcZ3, edges)
  }

  logger.write(Logger.Level.RESULT, "Using bounded portfolio\n")

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
