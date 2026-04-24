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
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection.DATA_RACE
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.LoopUnrollPass

fun hornPortfolio(
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
          enableDataRaceToReachability =
            portfolioConfig.inputConfig.property.verifiedProperty == DATA_RACE,
          specConfig = CFrontendConfig(arithmetic = ArchitectureConfig.ArithmeticType.efficient),
        ),
      backendConfig =
        BackendConfig(
          backend = Backend.CHC,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          specConfig = HornConfig(solver = "Z3:new", validateSolver = false),
        ),
      outputConfig = getDefaultOutputConfig(portfolioConfig),
      debugConfig = portfolioConfig.debugConfig,
    )

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
    solver: String = "Z3:new",
    timeoutMs: Long = 0,
    inProcess: Boolean = this.backendConfig.inProcess,
  ): XcfaConfig<*, HornConfig> {
    return copy(
      backendConfig =
        backendConfig.copy(
          timeoutMs = timeoutMs,
          inProcess = inProcess,
          parseInProcess = inProcess && portfolioConfig.backendConfig.parseInProcess,
          specConfig = backendConfig.specConfig!!.copy(solver = solver),
        )
    )
  }

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()
    val configEldarica =
      ConfigNode(
        "Eldarica-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, solver = "eldarica:2.2", timeoutMs = 500_000),
        checker,
      )
    val configGolem =
      ConfigNode(
        "Golem-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, solver = "golem:0.9.0", timeoutMs = 300_000),
        checker,
      )
    val configZ3native =
      ConfigNode(
        "Z3native-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, solver = "Z3:new", timeoutMs = 100_000),
        checker,
      )
    val configZ3 =
      ConfigNode(
        "Z3-$inProcess",
        baseConfig.adaptConfig(inProcess = inProcess, solver = "z3:4.15.3", timeoutMs = 100_000),
        checker,
      )

    edges.add(Edge(configEldarica, configGolem, anyError))
    edges.add(Edge(configGolem, configZ3native, anyError))
    edges.add(Edge(configZ3native, configZ3, anyError))

    return STM(configEldarica, edges)
  }

  logger.benchmark("Using CHC portfolio\n")

  if (parseContext.arithmeticTraits.contains(ArithmeticTrait.FLOAT)) {
    throw UnsupportedOperationException("CHC portfolio does not support floating points")
  }

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
