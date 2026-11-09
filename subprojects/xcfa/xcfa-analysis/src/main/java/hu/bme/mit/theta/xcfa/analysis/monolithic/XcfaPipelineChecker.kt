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
import hu.bme.mit.theta.xcfa.witnesses.hasInvariantChecks

class XcfaPipelineChecker<Pr : InvariantProof>
@JvmOverloads
constructor(
  private val xcfa: XCFA,
  private val property: XcfaProperty,
  private val parseContext: ParseContext,
  private val checkerFactory:
    (MonolithicExpr) -> SafetyChecker<out Pr, Trace<ExplState, ExprAction>, UnitPrec>,
  private val passes: MutableList<MonolithicExprPass<Pr>> = mutableListOf(),
  private val logger: Logger = NullLogger.getInstance(),
  private val acceptUnreliableSafe: Boolean,
  private val initValues: Boolean = false,
  private val blockEncoding: Boolean = false,
  /** The loop unroll bound to start from; 0 tries without unrolling first. */
  forceUnrollBound: Int = 0,
) :
  FormalismPipelineChecker<
    XCFA,
    XcfaState<PtrState<ExplState>>,
    XcfaAction,
    Pr,
    LocationInvariants,
  >(
    if (parseContext.multiThreading) {
      check(!xcfa.hasInvariantChecks) {
        "Witness invariants are checked only in sequential programs"
      }
      if (forceUnrollBound > 0) {
        XcfaMultiThreadToMonolithicAdapter(xcfa, property, parseContext, initValues, forceUnrollBound)
      } else try {
        XcfaMultiThreadToMonolithicAdapter(xcfa, property, parseContext, initValues)
      } catch (e: IllegalStateException) {
        if (
          "XcfaMultiThreadToMonolithicAdapter does not support these labels in a loop" in
            (e.message ?: "")
        ) {
          logger.info(
            "Multithreaded XCFA to monolithic expression transformation failed, falling back to force unrolling loops."
          )
          XcfaMultiThreadToMonolithicAdapter(
            xcfa,
            property,
            parseContext,
            initValues,
            FIRST_FORCE_UNROLL_BOUND,
          )
        } else throw e
      }
    } else {
      XcfaSingleThreadToMonolithicAdapter(xcfa, property, parseContext, initValues, blockEncoding)
    },
    MEPipelineCheckerConstructorArguments(checkerFactory, passes, logger = logger),
  ) {

  override fun check(
    input: UnitPrec?
  ): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>> {
    val result = super.check(input)
    logger.mainStep("XcfaPipelineChecker result: $result")
    if (result.isSafe && modelAdapter.model.unsafeUnrollUsed && !acceptUnreliableSafe) {
      logger.mainStep("Incomplete loop unroll used: safe result is unreliable.")
      // A violation within more iterations is still a real one, so a deeper unroll is worth a try.
      val bound = (modelAdapter as? XcfaMultiThreadToMonolithicAdapter)?.forceUnrollBound ?: 0
      if (bound in 1 until MAX_FORCE_UNROLL_BOUND) {
        logger.mainStep("Retrying with loops unrolled ${bound + 1} times.")
        return XcfaPipelineChecker(
            xcfa,
            property,
            parseContext,
            checkerFactory,
            passes,
            logger,
            acceptUnreliableSafe,
            initValues,
            blockEncoding,
            bound + 1,
          )
          .check(input)
      }
      logger.mainStep(SafetyResult.unknown<EmptyProof, Cex>().toString())
      throw NotSolvableException()
    }
    return result
  }

  companion object {
    private const val FIRST_FORCE_UNROLL_BOUND = 2
    private const val MAX_FORCE_UNROLL_BOUND = 5
  }
}

internal val LitExpr<*>.value: Int
  get() =
    when (this) {
      is IntLitExpr -> value.toInt()
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this).toInt()
      else -> error("Unknown integer type: $type")
    }
