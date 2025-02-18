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
package hu.bme.mit.theta.xsts.cli

import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.enum
import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.*
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.hu.bme.mit.theta.xsts.analysis.toMonolithicExpr
import hu.bme.mit.theta.xsts.analysis.hu.bme.mit.theta.xsts.analysis.valToAction
import hu.bme.mit.theta.xsts.analysis.hu.bme.mit.theta.xsts.analysis.valToState
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

typealias S = XstsState<ExplState>

class XstsCliBounded :
  XstsCliMonolithicBasedCommand(
    name = "BOUNDED",
    help =
      "Bounded model checking algorithms (BMC, IMC, KINDUCTION). Use --variant to select the algorithm (by default BMC is selected).",
  ) {

  enum class Variant {
    BMC {

      override fun buildChecker(
        monolithicExpr: MonolithicExpr,
        solverFactory: SolverFactory,
        valToState: (Valuation) -> S,
        biValToAction: (Valuation, Valuation) -> XstsAction,
        logger: Logger,
      ) = buildBMC(monolithicExpr, solverFactory.createSolver(), valToState, biValToAction, logger)
    },
    KINDUCTION {

      override fun buildChecker(
        monolithicExpr: MonolithicExpr,
        solverFactory: SolverFactory,
        valToState: (Valuation) -> S,
        biValToAction: (Valuation, Valuation) -> XstsAction,
        logger: Logger,
      ) =
        buildKIND(
          monolithicExpr,
          solverFactory.createSolver(),
          solverFactory.createSolver(),
          valToState,
          biValToAction,
          logger,
        )
    },
    IMC {

      override fun buildChecker(
        monolithicExpr: MonolithicExpr,
        solverFactory: SolverFactory,
        valToState: (Valuation) -> S,
        biValToAction: (Valuation, Valuation) -> XstsAction,
        logger: Logger,
      ) =
        buildIMC(
          monolithicExpr,
          solverFactory.createSolver(),
          solverFactory.createItpSolver(),
          valToState,
          biValToAction,
          logger,
        )
    };

    abstract fun buildChecker(
      monolithicExpr: MonolithicExpr,
      solverFactory: SolverFactory,
      valToState: (Valuation) -> S,
      biValToAction: (Valuation, Valuation) -> XstsAction,
      logger: Logger,
    ): BoundedChecker<S, XstsAction>
  }

  private val variant by option().enum<Variant>().default(Variant.BMC)

  private fun printResult(
    status: SafetyResult<EmptyProof, Trace<S, XstsAction>>,
    xsts: XSTS,
    totalTimeMs: Long,
  ) {
    if (!outputOptions.benchmarkMode) return
    printCommonResult(status, xsts, totalTimeMs)
    val stats = status.stats.orElse(BoundedStatistics(0)) as BoundedStatistics
    listOf(stats.iterations).forEach(writer::cell)
    writer.newRow()
  }

  override fun run() {
    try {
      doRun()
    } catch (e: Exception) {
      printError(e)
      exitProcess(1)
    }
  }

  private fun doRun() {
    registerSolverManagers()
    val solverFactory = SolverManager.resolveSolverFactory(solver)
    val xsts = inputOptions.loadXsts()
    val monolithicExpr = createMonolithicExpr(xsts)
    val sw = Stopwatch.createStarted()
    val checker =
      variant.buildChecker(
        monolithicExpr,
        solverFactory,
        xsts::valToState,
        xsts::valToAction,
        logger,
      )
    val result = checker.check()
    sw.stop()
    printResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
    writeCex(result, xsts)
  }
}
