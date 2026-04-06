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
import com.github.ajalt.clikt.parameters.types.enum
import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.*
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import java.util.concurrent.TimeUnit

class XstsCliBounded :
  XstsCliMonolithicBaseCommand(
    name = "BOUNDED",
    help =
      "Bounded model checking algorithms (BMC, IMC, KINDUCTION). Use --variant to select the algorithm (by default BMC is selected).",
  ) {

  enum class Variant {
    BMC {

      override fun buildChecker(
        monolithicExpr: MonolithicExpr,
        solverFactory: SolverFactory,
      ) = buildBMC(monolithicExpr, solverFactory.createSolver())
    },
    KINDUCTION {

      override fun buildChecker(
        monolithicExpr: MonolithicExpr,
        solverFactory: SolverFactory,
      ) =
        buildKIND(
          monolithicExpr,
          solverFactory.createSolver(),
          solverFactory.createSolver(),
        )
    },
    IMC {

      override fun buildChecker(
        monolithicExpr: MonolithicExpr,
        solverFactory: SolverFactory,
      ) =
        buildIMC(
          monolithicExpr,
          solverFactory.createSolver(),
          solverFactory.createItpSolver(),
        )
    };

    abstract fun buildChecker(
      monolithicExpr: MonolithicExpr,
      solverFactory: SolverFactory,
    ): BoundedChecker
  }

  private val variant by option().enum<Variant>().default(Variant.BMC)

  override fun printExtraBenchmarkCells(status: SafetyResult<*, *>) {
    val stats = status.stats.orElse(BoundedStatistics(0)) as BoundedStatistics
    listOf(stats.iterations).forEach(writer::cell)
  }

  override fun doRun() {
    val solverFactory = SolverManager.resolveSolverFactory(solver)
    val xsts = inputOptions.loadXsts()
    val sw = Stopwatch.createStarted()
    val checker =
      createChecker(xsts, solverFactory) { variant.buildChecker(it, solverFactory) }
    val result = checker.check()
    sw.stop()
    printBenchmarkResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
    writeCex(result, xsts)
  }
}
