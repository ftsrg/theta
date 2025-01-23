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

import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.chc.CexTree
import hu.bme.mit.theta.analysis.algorithm.chc.HornChecker
import hu.bme.mit.theta.analysis.algorithm.chc.Invariant
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.toRelations
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

class XstsCliChc :
  XstsCliBaseCommand(name = "CHC", help = "Model checking using the Horn solving backend") {

  override val defaultSolver: String = "z3:4.13.0"

  private fun printResult(status: SafetyResult<Invariant, CexTree>, xsts: XSTS, totalTimeMs: Long) {
    if (!outputOptions.benchmarkMode) return
    printCommonResult(status, xsts, totalTimeMs)
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
    val checker = HornChecker(xsts.toRelations(), solverFactory, logger)
    val result = checker.check()
    sw.stop()
    printResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
  }
}
