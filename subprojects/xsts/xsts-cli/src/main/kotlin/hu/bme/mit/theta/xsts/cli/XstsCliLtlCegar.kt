/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import com.github.ajalt.clikt.parameters.groups.provideDelegate
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.help
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.enum
import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.asg.ASG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.multi.MultiSide
import hu.bme.mit.theta.analysis.multi.NextSideFunctions
import hu.bme.mit.theta.analysis.multi.NextSideFunctions.Alternating
import hu.bme.mit.theta.analysis.multi.stmt.ExprMultiState
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.cfa.analysis.CfaState
import hu.bme.mit.theta.common.cfa.buchi.hoa.ExternalLtl2Hoaf
import hu.bme.mit.theta.common.cfa.buchi.hoa.Ltl2BuchiThroughHoaf
import hu.bme.mit.theta.common.ltl.LtlChecker
import hu.bme.mit.theta.common.ltl.cli.LtlCliOptions
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.*
import hu.bme.mit.theta.xsts.passes.XstsNormalizerPass
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

private typealias NSF<D> =
  NextSideFunctions.NextSideFunction<
    XstsState<UnitState>,
    CfaState<UnitState>,
    D,
    ExprMultiState<XstsState<UnitState>, CfaState<UnitState>, D>,
  >

class XstsLtlCliOptions() : LtlCliOptions() {
  enum class EnvtranSeparation() {
    COMBINED {

      override fun <D : ExprState> getNextsideFunction():
        NextSideFunctions.NextSideFunction<
          XstsState<UnitState>,
          CfaState<UnitState>,
          D,
          ExprMultiState<XstsState<UnitState>, CfaState<UnitState>, D>,
        > {
        return Alternating()
      }
    },
    SEPARATE {

      override fun <D : ExprState> getNextsideFunction(): NSF<D> = NSF { ms ->
        if (ms.sourceSide == MultiSide.RIGHT || ms.leftState.lastActionWasEnv()) MultiSide.LEFT
        else MultiSide.RIGHT
      }
    };

    abstract fun <D : ExprState> getNextsideFunction():
      NextSideFunctions.NextSideFunction<
        XstsState<UnitState>,
        CfaState<UnitState>,
        D,
        ExprMultiState<XstsState<UnitState>, CfaState<UnitState>, D>,
      >
  }

  val envtranSeparation: EnvtranSeparation by
    option(
        help =
          "Whether Buchi evaluation should happen between env and trans transitions or not (SEPARATED and COMBINED, respectively)"
      )
      .enum<EnvtranSeparation>()
      .default(EnvtranSeparation.SEPARATE)
}

class XstsCliLtlCegar :
  XstsCliBaseCommand(
    name = "LTLCEGAR",
    help = "Model checking using the CEGAR algorithm with an LTL property",
  ) {

  private val domain: Domain by
    option(help = "Abstraction domain to use").enum<Domain>().default(Domain.PRED_CART)
  private val refinement: Refinement by
    option(help = "Refinement strategy to use").enum<Refinement>().default(Refinement.SEQ_ITP)
  private val predsplit: PredSplit by option().enum<PredSplit>().default(PredSplit.ATOMS)
  private val refinementSolver: String? by option(help = "Use a different solver for abstraction")
  private val abstractionSolver: String? by option(help = "Use a different solver for refinement")
  private val initprec: InitPrec by option().enum<InitPrec>().default(InitPrec.EMPTY)
  private val ltlOptions by XstsLtlCliOptions()

  private fun printResult(
    status: SafetyResult<out ASG<*, *>?, out ASGTrace<*, *>?>,
    xsts: XSTS,
    totalTimeMs: Long,
  ) {
    if (!outputOptions.benchmarkMode) return
    printCommonResult(status, xsts, totalTimeMs)
    val stats = status.stats.orElse(CegarStatistics(0, 0, 0, 0)) as CegarStatistics
    listOf(
        stats.algorithmTimeMs,
        stats.abstractorTimeMs,
        stats.refinerTimeMs,
        stats.iterations,
        0,
        0,
        0,
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
    val abstractionSolverFactory = SolverManager.resolveSolverFactory(abstractionSolver ?: solver)
    val refinementSolverFactory = SolverManager.resolveSolverFactory(refinementSolver ?: solver)
    val xsts = XstsNormalizerPass.transform(inputOptions.loadXsts())
    val config =
      XstsConfigBuilder(domain, refinement, abstractionSolverFactory, refinementSolverFactory)
        .initPrec(initprec)
        .predSplit(predsplit)
    if (domain == Domain.EXPL) {
      val configBuilder = config.ExplStrategy(xsts)
      val checker =
        LtlChecker(
          configBuilder.multiSide,
          configBuilder.lts,
          configBuilder.itpRefToPrec,
          configBuilder.itpRefToPrec,
          configBuilder.dataAnalysis,
          ltlOptions.ltlExpression,
          abstractionSolverFactory,
          logger,
          ltlOptions.searchStrategy,
          ltlOptions.refinerStrategy,
          Ltl2BuchiThroughHoaf(ExternalLtl2Hoaf(ltlOptions.ltl2BuchiCommand), logger),
          xsts.vars,
          xsts.initFormula,
          ltlOptions.envtranSeparation.getNextsideFunction(),
        )
      val sw = Stopwatch.createStarted()
      val result = checker.check(configBuilder.initPrec, configBuilder.initPrec)
      sw.stop()
      printResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
      writeCex(result, xsts)
    }
    if (domain in setOf(Domain.PRED_CART, Domain.PRED_SPLIT, Domain.PRED_BOOL)) {
      val configBuilder = config.PredStrategy(xsts)
      val checker =
        LtlChecker(
          configBuilder.multiSide,
          configBuilder.lts,
          configBuilder.itpRefToPrec,
          configBuilder.itpRefToPrec,
          configBuilder.dataAnalysis,
          ltlOptions.ltlExpression,
          abstractionSolverFactory,
          logger,
          ltlOptions.searchStrategy,
          ltlOptions.refinerStrategy,
          Ltl2BuchiThroughHoaf(ExternalLtl2Hoaf(ltlOptions.ltl2BuchiCommand), logger),
          xsts.vars,
          xsts.initFormula,
          NextSideFunctions.Alternating(),
        )
      val sw = Stopwatch.createStarted()
      val result = checker.check(configBuilder.initPrec, configBuilder.initPrec)
      sw.stop()
      printResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
      writeCex(result, xsts)
    }
  }
}
