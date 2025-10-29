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
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.DirectionalMonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassResult
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.exception.MEPassPipelineException
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction

/**
 * This pass checks if the trace has changed since the last iteration. If it has not, it throws an
 * exception.
 */
class TraceChangeCheckMEPass<Pr : InvariantProof> : DirectionalMonolithicExprPass<Pr> {

  private var lastResult: SafetyResult<Pr, Trace<ExplState, ExprAction>>? = null

  override fun backward(
    safetyResult: SafetyResult<Pr, Trace<ExplState, ExprAction>>
  ): MonolithicExprPassResult<Pr> {
    if (
      lastResult != null &&
        safetyResult.isUnsafe &&
        lastResult!!.isUnsafe &&
        safetyResult.asUnsafe().cex == lastResult!!.asUnsafe().cex
    ) {
      throw UnchangedTraceException
    }
    lastResult = safetyResult
    return MonolithicExprPassResult(safetyResult)
  }

  object UnchangedTraceException : MEPassPipelineException("Trace did not change")
}
