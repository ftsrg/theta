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
package hu.bme.mit.theta.xsts.cli

import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.boolean
import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.algorithm.ic3.Ic3Checker
import hu.bme.mit.theta.solver.SolverManager
import java.util.concurrent.TimeUnit

class XstsCliIC3 :
  XstsCliMonolithicBaseCommand(name = "IC3", help = "Model checking using the IC3 algorithm.") {

  private val formerFramesOpt: Boolean by option().boolean().default(true)
  private val unSatOpt: Boolean by option().boolean().default(true)
  private val notBOpt: Boolean by option().boolean().default(true)
  private val propagateOpt: Boolean by option().boolean().default(true)
  private val filterOpt: Boolean by option().boolean().default(true)

  override fun doRun() {
    val solverFactory = SolverManager.resolveSolverFactory(solver)
    val xsts = inputOptions.loadXsts()
    val sw = Stopwatch.createStarted()
    val checker =
      createChecker(xsts, solverFactory) {
        Ic3Checker(
          it,
          solverFactory,
          formerFramesOpt,
          unSatOpt,
          notBOpt,
          propagateOpt,
          filterOpt,
          true,
        )
      }
    val result = checker.check()
    sw.stop()
    printBenchmarkResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
    writeCex(result, xsts)
  }
}
