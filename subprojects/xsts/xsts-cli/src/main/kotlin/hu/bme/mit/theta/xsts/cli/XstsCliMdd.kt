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
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.enum
import com.github.ajalt.clikt.parameters.types.file
import com.github.ajalt.clikt.parameters.types.long
import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.mdd.MddAnalysisStatistics
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.orderVars
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.xsts.XSTS
import java.io.File
import java.util.concurrent.TimeUnit

class XstsCliMdd :
  XstsCliMonolithicBaseCommand(
    name = "MDD",
    help = "Model checking of XSTS using MDDs (Multi-value Decision Diagrams)",
  ) {

  private val ordering: File? by
    option(help = "Path to a file containing variable ordering (one name per line)")
      .file(mustExist = true, canBeDir = false, mustBeReadable = true)

  private val dumpOrdering: Boolean by
    option("--dump-ordering", help = "Dump the computed variable ordering to <model>.ordering")
      .flag()

  private val iterationStrategy: MddChecker.IterationStrategy by
    option(help = "The state space enumeration algorithm to use")
      .enum<MddChecker.IterationStrategy>()
      .default(MddChecker.IterationStrategy.GSAT)

  private val mddToExprStrategy: MddExpressionRepresentation.MddToExprStrategy by
    option(help = "The MDD to expression conversion strategy")
      .enum<MddExpressionRepresentation.MddToExprStrategy>()
      .default(MddExpressionRepresentation.MddToExprStrategy.VARIABLE_LEVEL)

  private val proofMddToExprStrategy: MddExpressionRepresentation.MddToExprStrategy by
    option(help = "The MDD to expression conversion strategy for the proof invariant")
      .enum<MddExpressionRepresentation.MddToExprStrategy>()
      .default(MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL)

  private val traceTimeout: Long by
    option(help = "The timeout for trace generation in seconds (0 for no timeout)")
      .long()
      .default(10)

  private fun loadOrdering(monolithicExpr: MonolithicExpr): List<VarDecl<*>> {
    val file = ordering ?: return monolithicExpr.orderVars()
    require(!livenessToSafety) {
      "Variable ordering cannot be used with liveness-to-safety transformation (L2S modifies variables)"
    }
    require(!cegar) {
      "Variable ordering cannot be used with CEGAR (predicate abstraction modifies variables)"
    }
    val varsByName = monolithicExpr.vars.associateBy { it.name }
    val result = file.readLines()
      .map { it.trim() }
      .takeWhile { it != "#END" }
      .filter { it.isNotBlank() && !it.startsWith("#") }
      .map { name ->
        val xstsName = name.replace(".", "_").replace("[", "_").replace("]", "")
        varsByName[xstsName]
          ?: throw IllegalArgumentException(
            "Variable '$name' (normalized: '$xstsName') from ordering file not found in model. Available variables: ${varsByName.keys}"
          )
      }
      .reversed()
    val missing = monolithicExpr.vars.toSet() - result.toSet()
    require(missing.isEmpty()) {
      "Ordering file is missing variables: ${missing.map { it.name }}"
    }
    return result
  }

  override fun printExtraBenchmarkCells(status: SafetyResult<*, *>) {
    val stats =
      status.stats.orElse(MddAnalysisStatistics(0, 0, 0, 0, 0, 0, 0)) as MddAnalysisStatistics
    listOf(
        stats.violatingSize,
        stats.stateSpaceSize,
        stats.hitCount,
        stats.queryCount,
        stats.cacheSize,
      )
      .forEach(writer::cell)
  }

  override fun doRun() {
    val solverFactory = SolverManager.resolveSolverFactory(solver)
    val xsts = inputOptions.loadXsts()
    val sw = Stopwatch.createStarted()
    val result =
      SolverPool(solverFactory).use { solverPool ->
        val checker =
          createChecker(xsts, solverFactory) {
            val variableOrdering = loadOrdering(it)
            dumpOrdering(variableOrdering)
            MddChecker(
              it,
              solverPool,
              logger,
              iterationStrategy,
              variableOrdering = variableOrdering,
              mddToExprStrategy = mddToExprStrategy,
              proofMddToExprStrategy = proofMddToExprStrategy,
              traceTimeout = traceTimeout,
            )
          }
        checker.check(null)
      }
    sw.stop()
    printBenchmarkResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
    writeCex(result, xsts)
  }

  private fun dumpOrdering(variableOrdering: List<VarDecl<*>>) {
    if (!dumpOrdering) return
    val file = File("${inputOptions.model.path}.ordering")
    val traceability = inputOptions.variableTraceability
    // Ordering is stored reversed internally; reverse back for top-down file format
    val lines = variableOrdering.reversed().map { v -> traceability[v] ?: v.name }
    file.writeText(lines.joinToString("\n") + "\n")
    logger.writeln(Logger.Level.MAINSTEP, "Variable ordering dumped to ${file.path}")
  }
}
