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

import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MEPipelineCheckerConstructorArguments
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.L2SMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.PredicateAbstractionMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.ReverseMEPass
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.pipeline.XstsPipelineChecker

abstract class XstsCliMonolithicBaseCommand(name: String? = null, help: String = "") :
  XstsCliBaseCommand(name = name, help = help) {

  protected val reversed: Boolean by option(help = "Reversed state space exploration").flag()
  private val livenessToSafety: Boolean by
    option(help = "Use liveness to safety transformation").flag()
  private val cegar: Boolean by option(help = "Wrap analysis in CEGAR loop").flag()

  fun <Pr : InvariantProof> createChecker(
    xsts: XSTS,
    solverFactory: SolverFactory,
    checkerFactory: (MonolithicExpr) -> SafetyChecker<Pr, Trace<ExplState, ExprAction>, UnitPrec>,
  ): SafetyChecker<InvariantProof, out Trace<XstsState<out ExprState>, XstsAction>, UnitPrec> {
    val passes = mutableListOf<MonolithicExprPass<Pr>>()
    if (livenessToSafety) {
      passes.add(L2SMEPass())
    }
    if (reversed) {
      passes.add(ReverseMEPass())
    }
    if (cegar) {
      passes.add(
        PredicateAbstractionMEPass(
          traceCheckerFactory = { model: MonolithicExpr ->
            ExprTraceFwBinItpChecker.create(
              model.initExpr,
              Not(model.propExpr),
              solverFactory.createItpSolver(),
            )
          }
        )
      )
    }
    return XstsPipelineChecker(xsts, MEPipelineCheckerConstructorArguments(checkerFactory, passes))
  }
}
