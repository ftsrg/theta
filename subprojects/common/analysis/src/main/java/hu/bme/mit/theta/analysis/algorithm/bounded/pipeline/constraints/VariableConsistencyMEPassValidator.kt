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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.constraints

import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassValidator
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.PipelineDirection
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.PipelineStep
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.exception.MEPassPipelineException
import hu.bme.mit.theta.core.decl.VarDecl

object VariableConsistencyMEPassValidator : MonolithicExprPassValidator<InvariantProof> {
  override fun checkStepResult(steps: List<PipelineStep<out InvariantProof>>) {
    val lastResult = steps.last().second
    val upstreamPassIndex = steps.last().first - 1
    if (
      lastResult.direction == PipelineDirection.FORWARD ||
        lastResult.safetyResult!!.isSafe ||
        upstreamPassIndex < 0
    )
      return
    val upstreamOutput =
      steps.findLast { it.first == upstreamPassIndex }!!.second.expressionResult!!
    lastResult.safetyResult
      .asUnsafe()
      .cex
      .states
      .flatMap { it.decls }
      .filterIsInstance<VarDecl<*>>()
      .forEach {
        if (it !in upstreamOutput.vars)
          throw MEPassPipelineException(
            "Trace contains variables not present in input monolithic expression for this pass"
          )
      }
  }
}
