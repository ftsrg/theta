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
import hu.bme.mit.theta.xcfa.cli.checkers.checkDssSupports
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA

/** First budget of a block checker; it grows 4-fold per round (see `DssCheckerRoster`). */
private const val EMERGENT_CHECKER_BUDGET_MS = 30_000L

/** Of the block checkers and DSS's own queries; legacy Z3 is far slower on floats. */
private const val EMERGENT_SOLVER = "JavaSMT:MATHSAT5"

/** Retried on when MathSAT fails a block. */
private const val EMERGENT_FALLBACK_SOLVER = "Z3:new"

/** Only DSS; fails on properties that no pass reduces to error-location reachability. */
fun emergent27(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {
  checkDssSupports(portfolioConfig.inputConfig.property)

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  val baseDssConfig = baseDssConfig(portfolioConfig)

  fun getStm(inProcess: Boolean): STM {
    val dss =
      ConfigNode(
        "DSS-MIN_CUT_ABSORB_SELF_LOOPS-KIND-CEGAR-EXPL-BUDGET-CUT-$inProcess",
        baseDssConfig.copy(
          backendConfig =
            baseDssConfig.backendConfig.copy(
              timeoutMs = 0,
              inProcess = inProcess,
              specConfig =
                baseDssConfig.backendConfig.specConfig!!.copy(
                  decomposition = DssDecomposition.MIN_CUT_ABSORB_SELF_LOOPS,
                  // A whole-loop block usually needs k-induction; the budget keeps a checker that
                  // cannot finish from starving the others
                  checkerBackends = listOf(Backend.KIND, Backend.CEGAR),
                  checkerSelection = DssCheckerSelectionMethod.PRIORITY,
                  checkerBudgetMs = EMERGENT_CHECKER_BUDGET_MS,
                  cutOnTimeout = true,
                  explChecker = true,
                  solver = EMERGENT_SOLVER,
                  fallbackSolver = EMERGENT_FALLBACK_SOLVER,
                  blockLocalPool = true,
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
