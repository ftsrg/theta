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

import hu.bme.mit.theta.analysis.algorithm.Result
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.cli.checkers.checkDssSupports
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA

/** First budget of a block checker; it grows 4-fold per round (see `DssCheckerRoster`). */
private const val EMERGENT_CHECKER_BUDGET_MS = 90_000L

/** Of the block checkers and DSS's own queries; legacy Z3 is far slower on floats. */
private const val EMERGENT_SOLVER = "JavaSMT:MATHSAT5"

/** Retried on when MathSAT fails a block. */
private const val EMERGENT_FALLBACK_SOLVER = "Z3:new"

/** Replaces MathSAT on nonlinear integer programs without floats or bitwise operations. */
private const val EMERGENT_NONLINEAR_SOLVER = "Z3:new"

/** Wall-clock slice of the lead configuration; it solves most of its tasks well within it. */
private const val EMERGENT_LEAD_SLICE_MS = 200_000L

/** Wall-clock slice of the CEGAR-only configuration; its own tasks are solved fast. */
private const val EMERGENT_CEGAR_SLICE_MS = 450_000L

/**
 * Only DSS; fails on properties that no pass reduces to error-location reachability.
 *
 * Three DSS configurations in sequence, as they complement each other: the budgeted MathSAT run
 * leads, CEGAR blocks on legacy Z3 take the event-condition-action and product-line programs it
 * misses, and KIND-first blocks without a budget get the rest of the time, for the deep float and
 * bit-vector loops that a budget cuts off.
 */
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
  // An unknown is no verdict, so every step but the last hands over on it as on a failure
  val handOverOnUnknown = { config: XcfaConfig<*, *> ->
    checker(config).also {
      if (it is SafetyResult<*, *> && !it.isSafe && !it.isUnsafe) {
        throw ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code)
      }
    }
  }

  val baseDssConfig = baseDssConfig(portfolioConfig)

  fun dss(
    name: String,
    timeoutMs: Long,
    inProcess: Boolean,
    check: (XcfaConfig<*, *>) -> Result<*>,
    adapt: DssConfig.() -> DssConfig,
  ) =
    ConfigNode(
      "DSS-$name-$inProcess",
      baseDssConfig.copy(
        backendConfig =
          baseDssConfig.backendConfig.copy(
            timeoutMs = timeoutMs,
            inProcess = inProcess,
            specConfig = baseDssConfig.backendConfig.specConfig!!.adapt(),
          )
      ),
      check,
    )

  fun getStm(inProcess: Boolean): STM {
    val lead =
      dss("BUDGET-CUT", EMERGENT_LEAD_SLICE_MS, inProcess, handOverOnUnknown) {
        copy(
          decomposition = DssDecomposition.MIN_CUT_ABSORB_SELF_LOOPS,
          // A whole-loop block usually needs k-induction; the budget keeps a checker that cannot
          // finish from starving the others
          checkerBackends = listOf(Backend.KIND, Backend.CEGAR),
          checkerSelection = DssCheckerSelectionMethod.PRIORITY,
          checkerBudgetMs = EMERGENT_CHECKER_BUDGET_MS,
          // A block every checker times out on is cut in place into acyclic pieces
          cutOnTimeout = true,
          cutStrategy = DssDecomposition.MERGE_ACYCLIC,
          cutRestart = DssCutRestart.BLOCK,
          interpolateBoundedProofs = false,
          solver = EMERGENT_SOLVER,
          fallbackSolver = EMERGENT_FALLBACK_SOLVER,
          nonlinearSolver = EMERGENT_NONLINEAR_SOLVER,
        )
      }
    val cegar =
      dss("CEGAR-LEGACYZ3", EMERGENT_CEGAR_SLICE_MS, inProcess, handOverOnUnknown) {
        copy(
          decomposition = DssDecomposition.MIN_CUT_ABSORB_SELF_LOOPS,
          checkerBackends = listOf(Backend.CEGAR),
          cegarDomain = DssCegarDomain.PRED_CART,
          globalPredicatePool = false,
        )
      }
    val kind =
      dss("KIND-CEGAR-NOBUDGET", 0, inProcess, checker) {
        copy(
          decomposition = DssDecomposition.MIN_CUT_ABSORB_SELF_LOOPS,
          checkerBackends = listOf(Backend.KIND, Backend.CEGAR),
          checkerSelection = DssCheckerSelectionMethod.PRIORITY,
          cegarDomain = DssCegarDomain.PRED_CART,
          globalPredicatePool = false,
          interpolateBoundedProofs = false,
          solver = EMERGENT_SOLVER,
          fallbackSolver = EMERGENT_FALLBACK_SOLVER,
        )
      }
    return STM(lead, setOf(Edge(lead, cegar, anyError), Edge(cegar, kind, anyError)))
  }

  logger.benchmark("Using portfolio: DSS\n")

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
