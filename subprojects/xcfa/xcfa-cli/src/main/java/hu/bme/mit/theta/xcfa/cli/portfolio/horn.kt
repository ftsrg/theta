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

fun hornPortfolio25(
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
        portfolioConfig.inputConfig.copy(
          xcfaWCtx =
            if (portfolioConfig.backendConfig.parseInProcess) null
            else Triple(xcfa, mcm, parseContext),
          propertyFile = null,
          property = portfolioConfig.inputConfig.property,
        ),
      frontendConfig =
        FrontendConfig(
          lbeLevel = LbePass.defaultLevel,
          loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
          inputType = InputType.C,
          specConfig = CFrontendConfig(arithmetic = ArchitectureConfig.ArithmeticType.efficient),
        ),
      backendConfig =
        BackendConfig(
          backend = Backend.CHC,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          specConfig = HornConfig(solver = "z3:4.13.0", validateSolver = false),
        ),
      outputConfig = getDefaultOutputConfig(portfolioConfig),
      debugConfig = portfolioConfig.debugConfig,
    )

  if (parseContext.multiThreading) {
    throw UnsupportedOperationException("Multithreading for horn checkers not supported")
  }

  if (!xcfa.isInlined) {
    throw UnsupportedOperationException("Recursive XCFA for horn checkers not supported")
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

  fun XcfaConfig<*, HornConfig>.adaptConfig(
    solver: String = "z3:4.13.0",
    timeoutMs: Long = 0,
    inProcess: Boolean = this.backendConfig.inProcess,
  ): XcfaConfig<*, HornConfig> {
    return copy(
      backendConfig =
        backendConfig.copy(
          timeoutMs = timeoutMs,
          inProcess = inProcess,
          specConfig = backendConfig.specConfig!!.copy(solver = solver),
        )
    )
  }

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()
    val configZ3 =
      ConfigNode(
        "Z3-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, timeoutMs = 100_000),
        checker,
      )
    val configZ3native =
      ConfigNode(
        "Z3native-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, solver = "Z3:new", timeoutMs = 100_000),
        checker,
      )
    val configEldarica =
      ConfigNode(
        "Eldarica-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, solver = "eldarica:2.1", timeoutMs = 500_000),
        checker,
      )
    val configGolem =
      ConfigNode(
        "Golem-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, solver = "golem:0.5.0", timeoutMs = 300_000),
        checker,
      )

    edges.add(Edge(configZ3, configZ3native, anyError))
    edges.add(Edge(configZ3native, configEldarica, anyError))
    edges.add(Edge(configEldarica, configGolem, anyError))

    return STM(configZ3, edges)
  }

  logger.write(Logger.Level.RESULT, "Using CHC portfolio\n")

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
