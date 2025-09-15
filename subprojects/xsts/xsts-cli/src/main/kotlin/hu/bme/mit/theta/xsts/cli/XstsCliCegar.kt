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
import com.github.ajalt.clikt.parameters.types.int
import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.analysis.utils.TraceVisualizer
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.*
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

class XstsCliCegar :
  XstsCliBaseCommand(
    name = "CEGAR",
    help = "Model checking using the CEGAR (CounterExample Guided Abstraction Refinement) algorithm",
  ) {

  private val domain: Domain by
    option(help = "Abstraction domain to use").enum<Domain>().default(Domain.PRED_CART)
  private val refinement: Refinement by
    option(help = "Refinement strategy to use").enum<Refinement>().default(Refinement.SEQ_ITP)
  private val search: Search by
    option(help = "Search strategy to use").enum<Search>().default(Search.BFS)
  private val refinementSolver: String? by option(help = "Use a different solver for abstraction")
  private val abstractionSolver: String? by option(help = "Use a different solver for refinement")
  private val predsplit: PredSplit by option().enum<PredSplit>().default(PredSplit.WHOLE)
  private val maxenum: Int by option().int().default(0)
  private val autoexpl: AutoExpl by option().enum<AutoExpl>().default(AutoExpl.NEWOPERANDS)
  private val initprec: InitPrec by option().enum<InitPrec>().default(InitPrec.EMPTY)
  private val prunestrategy: PruneStrategy by
    option().enum<PruneStrategy>().default(PruneStrategy.LAZY)
  private val optimizestmts: OptimizeStmts by
    option().enum<OptimizeStmts>().default(OptimizeStmts.ON)

  private fun printResult(
    status: SafetyResult<out ARG<*, *>?, out Trace<*, *>?>,
    xsts: XSTS,
    totalTimeMs: Long,
  ) {
    if (!outputOptions.benchmarkMode) {
      logger.writeln(Logger.Level.RESULT, status.toString())
      return
    }
    printCommonResult(status, xsts, totalTimeMs)
    val stats = status.stats.orElse(CegarStatistics(0, 0, 0, 0)) as CegarStatistics
    listOf(
        stats.algorithmTimeMs,
        stats.abstractorTimeMs,
        stats.refinerTimeMs,
        stats.iterations,
        status.proof!!.size(),
        status.proof!!.depth,
        status.proof!!.meanBranchingFactor,
      )
      .forEach(writer::cell)
    writer.newRow()
  }

  private fun writeVisualStatus(
    status: SafetyResult<out ARG<*, *>?, out Trace<out State?, out Action?>?>
  ) {
    if (outputOptions.visualize == null) return
    val graph =
      if (status.isSafe) ArgVisualizer.getDefault().visualize(status.asSafe().proof)
      else TraceVisualizer.getDefault().visualize(status.asUnsafe().cex)
    GraphvizWriter.getInstance().writeFile(graph, outputOptions.visualize!!)
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
    val abstractionSolverFactory = SolverManager.resolveSolverFactory(abstractionSolver ?: solver)
    val refinementSolverFactory = SolverManager.resolveSolverFactory(refinementSolver ?: solver)
    val xsts = inputOptions.loadXsts()
    val config =
      XstsConfigBuilder(domain, refinement, abstractionSolverFactory, refinementSolverFactory)
        .maxEnum(maxenum)
        .autoExpl(autoexpl)
        .initPrec(initprec)
        .pruneStrategy(prunestrategy)
        .search(search)
        .predSplit(predsplit)
        .optimizeStmts(optimizestmts)
        .logger(logger)
        .build(xsts)
    val sw = Stopwatch.createStarted()
    val result = config.check()
    sw.stop()
    printResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
    writeCex(result, xsts)
    writeVisualStatus(result)
  }
}
