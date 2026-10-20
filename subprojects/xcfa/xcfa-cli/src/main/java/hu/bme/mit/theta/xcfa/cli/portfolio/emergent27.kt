/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA

/** Only DSS; properties other than error-location reachability go to [emergent26]. */
fun emergent27(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {
  if (portfolioConfig.inputConfig.property.verifiedProperty != ErrorDetection.ERROR_LOCATION)
    return emergent26(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  val baseDssConfig = baseDssConfig(portfolioConfig)

  fun getStm(inProcess: Boolean): STM {
    val dss =
      ConfigNode(
        "DSS-MIN_CUT_ABSORB_SELF_LOOPS-CEGAR_PRED_CART-KIND-$inProcess",
        baseDssConfig.copy(
          backendConfig =
            baseDssConfig.backendConfig.copy(
              timeoutMs = 0,
              inProcess = inProcess,
              specConfig =
                baseDssConfig.backendConfig.specConfig!!.copy(
                  decomposition = DssDecomposition.MIN_CUT_ABSORB_SELF_LOOPS,
                  checkerBackends =
                    listOf(DssCheckerBackend.CEGAR_PRED_CART, DssCheckerBackend.KIND),
                  checkerSelection = DssCheckerSelectionMethod.PRIORITY,
                ),
            )
        ),
        checker,
      )
    return STM(dss, emptySet())
  }

  logger.benchmark("Using portfolio: DSS\n")

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
