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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction

fun interface MonolithicExprPass<Pr : InvariantProof> {
  fun process(
    data: MonolithicExprPassResult<Pr>,
    status: MonolithicExprPipelineCheckerStatus,
  ): MonolithicExprPassResult<Pr>
}

interface DirectionalMonolithicExprPass<Pr : InvariantProof> : MonolithicExprPass<Pr> {

  override fun process(
    data: MonolithicExprPassResult<Pr>,
    status: MonolithicExprPipelineCheckerStatus,
  ): MonolithicExprPassResult<Pr> {
    return when (data.direction) {
      PipelineDirection.FORWARD -> forward(data.expressionResult!!)
      PipelineDirection.BACKWARD -> backward(data.safetyResult!!)
    }
  }

  fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> =
    MonolithicExprPassResult(monolithicExpr)

  fun backward(
    safetyResult: SafetyResult<Pr, Trace<ExplState, ExprAction>>
  ): MonolithicExprPassResult<Pr> = MonolithicExprPassResult(safetyResult)
}
