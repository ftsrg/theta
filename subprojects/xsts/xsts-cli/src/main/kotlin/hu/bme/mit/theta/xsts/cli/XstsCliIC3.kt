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
import com.github.ajalt.clikt.parameters.types.boolean
import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.ic3.Ic3Checker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.hu.bme.mit.theta.xsts.analysis.valToState
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

class XstsCliIC3 :
  XstsCliMonolithicBaseCommand(name = "IC3", help = "Model checking using the IC3 algorithm.") {

  private val formerFramesOpt: Boolean by option().boolean().default(true)
  private val unSatOpt: Boolean by option().boolean().default(true)
  private val notBOpt: Boolean by option().boolean().default(true)
  private val propagateOpt: Boolean by option().boolean().default(true)
  private val filterOpt: Boolean by option().boolean().default(true)

  private fun printResult(
    status: SafetyResult<EmptyProof, Trace<S, XstsAction>>,
    xsts: XSTS,
    totalTimeMs: Long,
  ) {
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
    val monolithicExpr = createMonolithicExpr(xsts)
    val sw = Stopwatch.createStarted()
    val checker =
      wrapInCegarIfNeeded(monolithicExpr, solverFactory) {
        Ic3Checker(
          it,
          !reversed,
          solverFactory,
          it.valToState,
          it.biValToAction,
          formerFramesOpt,
          unSatOpt,
          notBOpt,
          propagateOpt,
          filterOpt,
          true,
          logger,
        )
      }
    val result = checker.check()
    sw.stop()
    printResult(
      result as SafetyResult<EmptyProof, Trace<XstsState<ExplState>, XstsAction>>,
      xsts,
      sw.elapsed(TimeUnit.MILLISECONDS),
    )
    writeCex(result, xsts)
  }
}
