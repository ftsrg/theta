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
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.DirectionalMonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils

/** Reverses the model: swaps init and prop, and reverses the transition relation. */
class ReverseMEPass<Pr : InvariantProof> : DirectionalMonolithicExprPass<Pr> {

  lateinit var action: ExprAction

  override fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> {
    action = monolithicExpr.action()
    return MonolithicExprPassResult(
      monolithicExpr.let {
        it.copy(
          initExpr = Not(it.propExpr),
          transExpr = ExprUtils.reverse(it.transExpr, it.transOffsetIndex),
          propExpr = Not(it.initExpr),
        )
      }
    )
  }

  override fun backward(
    safetyResult: SafetyResult<Pr, Trace<ExplState, ExprAction>>
  ): MonolithicExprPassResult<Pr> {
    if (safetyResult.isUnsafe) {
      val states = safetyResult.asUnsafe().cex.states.reversed()
      return MonolithicExprPassResult(
        SafetyResult.unsafe(
          Trace.of(states, (1..<states.size).map { action }),
          safetyResult.asUnsafe().proof,
        )
      )
    }
    return MonolithicExprPassResult(safetyResult)
  }
}
