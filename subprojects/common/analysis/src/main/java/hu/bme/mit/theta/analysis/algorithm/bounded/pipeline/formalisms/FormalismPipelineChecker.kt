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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MEPipelineCheckerConstructorArguments
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassPipelineChecker
import hu.bme.mit.theta.analysis.unit.UnitPrec

/**
 * A checker that uses a [MonolithicExprPassPipelineChecker] and a [ModelToMonolithicAdapter] to
 * check the safety of a model with algorithms available for monolithic expressions. The class is
 * open to allow creation of convenience subclasses for specific formalisms.
 */
open class FormalismPipelineChecker<
  M,
  S : State,
  A : Action,
  InnerPr : InvariantProof,
  OuterPr : Proof,
>(
  val modelAdapter: ModelToMonolithicAdapter<M, S, A, OuterPr>,
  mePipelineFactory: (MonolithicExpr) -> MonolithicExprPassPipelineChecker<InnerPr>,
) : SafetyChecker<OuterPr, Trace<S, A>, UnitPrec> {

  constructor(
    modelAdapter: ModelToMonolithicAdapter<M, S, A, OuterPr>,
    pipelineArguments: MEPipelineCheckerConstructorArguments<InnerPr>,
  ) : this(
    modelAdapter,
    { monolithicExpr -> MonolithicExprPassPipelineChecker(monolithicExpr, pipelineArguments) },
  )

  private val monolithicExpr = modelAdapter.monolithicExpr
  private val pipeline = mePipelineFactory(monolithicExpr)

  override fun check(input: UnitPrec?): SafetyResult<OuterPr, Trace<S, A>> {
    val result = pipeline.check(input)
    return if (result.isSafe)
      SafetyResult.safe(modelAdapter.proofToModelProof(result.proof), result.stats.orElse(null))
    else
      SafetyResult.unsafe(
        modelAdapter.traceToModelTrace(result.asUnsafe().cex),
        modelAdapter.proofToModelProof(result.proof),
        result.stats.orElse(null),
      )
  }
}
