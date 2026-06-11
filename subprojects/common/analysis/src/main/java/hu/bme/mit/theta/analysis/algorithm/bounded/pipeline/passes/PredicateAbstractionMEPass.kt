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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.ImplicitPredicateAbstractor
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.DirectionalMonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType

/**
 * Implicit predicate abstraction as a pipeline pass, for checkers that cannot drive CEGAR
 * themselves: the pipeline's forward/backward loop plays the role of the refinement loop. The
 * abstraction itself is delegated to [ImplicitPredicateAbstractor]; CEGAR-aware checkers use that
 * class directly instead of this pass.
 */
class PredicateAbstractionMEPass<Pr : InvariantProof>
@JvmOverloads
constructor(
  private val traceCheckerFactory: (MonolithicExpr) -> ExprTraceChecker<ItpRefutation>,
  val initPrec: (MonolithicExpr) -> PredPrec = { monolithicExpr ->
    PredPrec.of(listOf(monolithicExpr.propExpr, monolithicExpr.initExpr))
  },
  val refine: (PredPrec, Expr<BoolType>) -> PredPrec = { prec, expr ->
    prec.join(PredPrec.of(expr))
  },
) : DirectionalMonolithicExprPass<Pr> {

  private lateinit var concreteModel: MonolithicExpr
  private lateinit var abstractor: ImplicitPredicateAbstractor
  private lateinit var currentPrec: PredPrec

  override fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> {
    concreteModel = monolithicExpr
    abstractor = ImplicitPredicateAbstractor(concreteModel)
    currentPrec = initPrec(concreteModel)
    return MonolithicExprPassResult(abstractor.abstractModel(currentPrec).model)
  }

  override fun backward(
    safetyResult: SafetyResult<Pr, Trace<ExplState, ExprAction>>
  ): MonolithicExprPassResult<Pr> {
    if (safetyResult.isSafe) {
      return MonolithicExprPassResult(safetyResult)
    }
    val trace = abstractor.toPredTrace(safetyResult.asUnsafe().cex)
    val concretizationResult = traceCheckerFactory(concreteModel).check(trace)
    if (concretizationResult.isFeasible) {
      val valuations = concretizationResult.asFeasible().valuations
      val prTraceUnsafe =
        SafetyResult.unsafe(
          valuations.run {
            Trace.of(states.map(ExplState::of), actions.map { concreteModel.action() })
          },
          safetyResult.proof,
        )
      return MonolithicExprPassResult(prTraceUnsafe)
    }
    val refutation = concretizationResult.asInfeasible().refutation
    currentPrec = refine(currentPrec, refutation[refutation.pruneIndex])
    return MonolithicExprPassResult(abstractor.abstractModel(currentPrec).model)
  }
}
