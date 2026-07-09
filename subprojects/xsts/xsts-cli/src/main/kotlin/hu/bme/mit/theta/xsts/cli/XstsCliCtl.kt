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
import com.github.ajalt.clikt.parameters.types.file
import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.mdd.MddProof
import hu.bme.mit.theta.analysis.algorithm.mdd.ctl.MddCtlChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.ctl.CtlParser
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.xsts.analysis.XstsToMonolithicAdapter
import java.io.File
import java.util.concurrent.TimeUnit

class XstsCliCtl :
  XstsCliBaseCommand(
    name = "CTL",
    help = "Symbolic CTL model checking of XSTS using MDDs (Multi-value Decision Diagrams)",
  ) {

  private val ctlProperty: File? by
    option(help = "Path of the CTL property file. Has priority over --ctl-expression")
      .file(mustExist = true, canBeDir = false, mustBeReadable = true)

  private val ctlExpression: String? by
    option(help = "CTL property as a string. Ignored if --ctl-property is defined")

  private val lookAheadStrategy: MddExpressionRepresentation.MddToExprStrategy by
    option(help = "The MDD to expression conversion strategy")
      .enum<MddExpressionRepresentation.MddToExprStrategy>()
      .default(MddExpressionRepresentation.MddToExprStrategy.VARIABLE_LEVEL)

  private val euStrategy: MddCtlChecker.EuStrategy by
    option(help = "The algorithm to compute E[p U q]")
      .enum<MddCtlChecker.EuStrategy>()
      .default(MddCtlChecker.EuStrategy.CONSTRAINED_SATURATION)

  override fun doRun() {
    val solverFactory = SolverManager.resolveSolverFactory(solver)
    // the XSTS prop block is irrelevant for CTL, but the grammar requires one
    val xsts = inputOptions.loadXsts(defaultProperty = "true")
    val monolithicExpr = XstsToMonolithicAdapter(xsts).monolithicExpr
    val propertyText =
      ctlProperty?.readText()
        ?: ctlExpression
        ?: throw IllegalArgumentException(
          "Missing CTL property: use --ctl-property or --ctl-expression"
        )
    val formula = CtlParser.parse(propertyText, monolithicExpr.vars)
    val sw = Stopwatch.createStarted()
    val result: SafetyResult<MddProof, Trace<ExplState, ExprAction>> =
      SolverPool(solverFactory).use { solverPool ->
        val checker =
          MddCtlChecker(
            monolithicExpr,
            solverPool,
            logger,
            lookAheadStrategy = lookAheadStrategy,
            euStrategy = euStrategy,
          )
        if (checker.isSatisfied(formula)) SafetyResult.safe(MddProof.of(checker.stateSpace))
        else
          SafetyResult.unsafe(
            Trace.of(listOf(ExplState.top()), listOf()),
            MddProof.of(checker.stateSpace),
          )
      }
    sw.stop()
    printBenchmarkResult(result, xsts, sw.elapsed(TimeUnit.MILLISECONDS))
  }
}
