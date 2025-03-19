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

/**
 * Represents the result of a monolithic expression pass. The direction indicates which pass the
 * pipeline should call next. The result contains either an expression or a safety result
 * corresponding to the direction. That is, if the direction is FORWARD, the result contains an
 * expression, and if the direction is BACKWARD, the result contains a safety result.
 */
data class MonolithicExprPassResult<Pr : InvariantProof>(
  val expressionResult: MonolithicExpr?,
  val safetyResult: SafetyResult<Pr, Trace<ExplState, ExprAction>>?,
  val direction: PipelineDirection,
  val hondaIndex: Int = -1,
) {
  constructor(
    expressionResult: MonolithicExpr
  ) : this(expressionResult, null, PipelineDirection.FORWARD)

  constructor(
    safetyResult: SafetyResult<Pr, Trace<ExplState, ExprAction>>
  ) : this(null, safetyResult, PipelineDirection.BACKWARD)

  init {
    check(expressionResult != null || safetyResult != null)
    check(direction != PipelineDirection.FORWARD || expressionResult != null)
    check(direction != PipelineDirection.BACKWARD || safetyResult != null)
  }
}
