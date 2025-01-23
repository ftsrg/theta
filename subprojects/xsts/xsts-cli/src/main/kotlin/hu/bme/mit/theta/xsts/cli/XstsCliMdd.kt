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
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.mdd.MddAnalysisStatistics
import hu.bme.mit.theta.analysis.algorithm.mdd.MddCex
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.MddProof
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.mdd.XstsMddChecker
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

class XstsCliMdd :
  XstsCliBaseCommand(
    name = "MDD",
    help = "Model checking of XSTS using MDDs (Multi-value Decision Diagrams)",
  ) {

  private val iterationStrategy: MddChecker.IterationStrategy by
    option(help = "The state space enumeration algorithm to use")
      .enum<MddChecker.IterationStrategy>()
      .default(MddChecker.IterationStrategy.GSAT)

  private fun printResult(status: SafetyResult<MddProof, MddCex>, xsts: XSTS, totalTimeMs: Long) {
    if (!outputOptions.benchmarkMode) return
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
    val sw = Stopwatch.createStarted()
    val result =
      SolverPool(solverFactory).use {
        val checker = XstsMddChecker.create(xsts, it, logger, iterationStrategy)
        checker.check(null)
      }
    sw.stop()
    printResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
  }
}
