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
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.mdd.MddAnalysisStatistics
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.MddProof
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import java.util.List
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

class XstsCliMdd :
  XstsCliMonolithicBaseCommand(
    name = "MDD",
    help = "Model checking of XSTS using MDDs (Multi-value Decision Diagrams)",
  ) {

  private val iterationStrategy: MddChecker.IterationStrategy by
    option(help = "The state space enumeration algorithm to use")
      .enum<MddChecker.IterationStrategy>()
      .default(MddChecker.IterationStrategy.GSAT)

  private fun printResult(
    status: SafetyResult<MddProof, Trace<XstsState<ExplState>, XstsAction>>,
    xsts: XSTS,
    totalTimeMs: Long,
  ) {
    if (!outputOptions.benchmarkMode) {
      logger.writeln(Logger.Level.RESULT, status.toString())
      return
    }
    printCommonResult(status, xsts, totalTimeMs)
    val stats = status.stats.orElse(MddAnalysisStatistics(0, 0, 0, 0, 0)) as MddAnalysisStatistics
    listOf(
        stats.violatingSize,
        stats.stateSpaceSize,
        stats.hitCount,
        stats.queryCount,
        stats.cacheSize,
      )
      .forEach(writer::cell)
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
    val result =
      SolverPool(solverFactory).use { solverPool ->
        val checker =
          wrapInCegarIfNeeded(monolithicExpr, solverFactory) {
            MddChecker.create(
              it,
              it.vars,
              solverPool,
              logger,
              MddChecker.IterationStrategy.GSAT,
              it.valToState,
              it.biValToAction,
              !reversed)
          }
        checker.check(null)
      }
    sw.stop()
    printResult(result as SafetyResult<MddProof, Trace<XstsState<ExplState>, XstsAction>>, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
    writeCex(result, xsts)
  }
}
