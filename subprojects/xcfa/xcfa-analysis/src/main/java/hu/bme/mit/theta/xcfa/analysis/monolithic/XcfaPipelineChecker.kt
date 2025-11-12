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
package hu.bme.mit.theta.xcfa.analysis.monolithic

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MEPipelineCheckerConstructorArguments
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.FormalismPipelineChecker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XCFA

class XcfaPipelineChecker<Pr : InvariantProof>
@JvmOverloads
constructor(
  xcfa: XCFA,
  property: XcfaProperty,
  parseContext: ParseContext,
  checkerFactory: (MonolithicExpr) -> SafetyChecker<out Pr, Trace<ExplState, ExprAction>, UnitPrec>,
  passes: MutableList<MonolithicExprPass<Pr>> = mutableListOf(),
  private val logger: Logger = NullLogger.getInstance(),
  private val acceptUnreliableSafe: Boolean,
  initValues: Boolean = false,
) :
  FormalismPipelineChecker<
    XCFA,
    XcfaState<PtrState<ExplState>>,
    XcfaAction,
    Pr,
    LocationInvariants,
  >(
    if (parseContext.multiThreading) {
      try {
        XcfaMultiThreadToMonolithicAdapter(xcfa, property, parseContext, initValues)
      } catch (e: IllegalStateException) {
        if (
          "XcfaMultiThreadToMonolithicAdapter does not support these labels in a loop" in
            (e.message ?: "")
        ) {
          logger.info(
            "Multithreaded XCFA to monolithic expression transformation failed, falling back to force unrolling loops."
          )
          XcfaMultiThreadToMonolithicAdapter(xcfa, property, parseContext, initValues, true)
        } else throw e
      }
    } else {
      XcfaSingleThreadToMonolithicAdapter(xcfa, property, parseContext, initValues)
    },
    MEPipelineCheckerConstructorArguments(checkerFactory, passes, logger = logger),
  ) {

  override fun check(
    input: UnitPrec?
  ): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>> =
    super.check(input).also {
      logger.mainStep("XcfaPipelineChecker result: $it")
      if (it.isSafe && modelAdapter.model.unsafeUnrollUsed && !acceptUnreliableSafe) {
        logger.mainStep("Incomplete loop unroll used: safe result is unreliable.")
        logger.result(SafetyResult.unknown<EmptyProof, Cex>().toString())
        throw NotSolvableException()
      }
    }
}

internal val LitExpr<*>.value: Int
  get() =
    when (this) {
      is IntLitExpr -> value.toInt()
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this).toInt()
      else -> error("Unknown integer type: $type")
    }
