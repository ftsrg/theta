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
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Domain.*
import hu.bme.mit.theta.xcfa.cli.params.Refinement.BW_BIN_ITP
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA

fun chcCompPortfolio25(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {
  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  val baseCegarConfig = baseCegarConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseBoundedConfig = baseBoundedConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseMddConfig = baseMddConfig(xcfa, mcm, parseContext, portfolioConfig, false)

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    val starExecPredBool =
      ConfigNode(
        "StarExec-PredBool-$inProcess",
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = PRED_BOOL,
          refinement = BW_BIN_ITP,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = 300_000,
        ),
        checker,
      )
    val starExecPredCart =
      ConfigNode(
        "StarExec-PredCart-$inProcess",
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = PRED_CART,
          refinement = BW_BIN_ITP,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = 300_000,
        ),
        checker,
      )

    val starExecExpl =
      ConfigNode(
        "StarExec-Expl-$inProcess",
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = EXPL,
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 300_000,
        ),
        checker,
      )
    edges.add(Edge(starExecPredBool, starExecPredCart, anythingButServerError))
    edges.add(Edge(starExecPredCart, starExecExpl, anythingButServerError))

    val startingConfig =
      if (xcfa.isInlined) {
        val quickBmcConfig =
          ConfigNode(
            "Bounded-BMC-$inProcess",
            baseBoundedConfig.adaptConfig(
              bmcEnabled = true,
              indEnabled = false,
              itpEnabled = false,
              timeoutMs = 50_000,
            ),
            checker,
          )

        val quickKindConfig =
          ConfigNode(
            "Bounded-KIND-$inProcess",
            baseBoundedConfig.adaptConfig(
              bmcEnabled = true,
              indEnabled = true,
              itpEnabled = false,
              timeoutMs = 300_000,
            ),
            checker,
          )

        edges.add(Edge(quickBmcConfig, quickKindConfig, anythingButServerError))

        val quickIMCConfig =
          ConfigNode(
            "Bounded-IMC-$inProcess",
            baseBoundedConfig.adaptConfig(
              bmcEnabled = false,
              indEnabled = false,
              itpEnabled = true,
              timeoutMs = 300_000,
            ),
            checker,
          )

        edges.add(Edge(quickKindConfig, quickIMCConfig, anythingButServerError))

        val quickMDDConfig =
          ConfigNode(
            "MDD-$inProcess",
            baseMddConfig.copy(
              backendConfig =
                baseMddConfig.backendConfig.copy(
                  timeoutMs = 50_000,
                  inProcess = inProcess,
                  parseInProcess = true,
                )
            ),
            checker,
          )

        edges.add(Edge(quickIMCConfig, quickMDDConfig, anythingButServerError))
        edges.add(Edge(quickMDDConfig, starExecPredBool, anythingButServerError))
        quickBmcConfig
      } else {
        starExecPredBool
      }

    val complex25 =
      ConfigNode(
        "Complex25-$inProcess",
        XcfaConfig(
          inputConfig =
            InputConfig(
              input = null,
              xcfaWCtx = Triple(xcfa, mcm, parseContext),
              propertyFile = null,
              property = portfolioConfig.inputConfig.property,
            ),
          frontendConfig = portfolioConfig.frontendConfig,
          backendConfig =
            (portfolioConfig.backendConfig as BackendConfig<PortfolioConfig>).copy(
              specConfig = PortfolioConfig("COMPLEX25")
            ),
          outputConfig = baseCegarConfig.outputConfig,
          debugConfig = portfolioConfig.debugConfig,
        ),
        checker,
      )

    edges.add(Edge(starExecExpl, complex25, anythingButServerError))

    return STM(startingConfig, edges)
  }

  val inProcessStm = getStm(true)
  val notInProcessStm = getStm(false)

  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
