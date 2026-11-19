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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.analysis.pred.ExprSplitters
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec
import hu.bme.mit.theta.analysis.pred.PredAbstractors
import hu.bme.mit.theta.analysis.pred.PredOrd
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.ItpRefToPtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.getPtrPartialOrd
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.XCFA
import java.util.concurrent.TimeUnit
import kotlin.random.Random
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

/**
 * Stack covering on a non-inlined XCFA, configured as the portfolios run recursive programs: the
 * stack partial order and lazy pruning.
 */
class XcfaStackPopTest {

  companion object {
    private val property = XcfaProperty(ErrorDetection.ERROR_LOCATION)

    @JvmStatic
    fun data(): Collection<Array<Any>> =
      listOf(
        arrayOf("/51stack_pop_global_effect_unsafe.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/51stack_pop_untouched_global_safe.c", SafetyResult<*, *>::isSafe),
      )
  }

  private fun parse(filepath: String): XCFA =
    getXcfaFromC(
        javaClass.getResourceAsStream(filepath)!!,
        ParseContext(),
        false,
        property,
        NullLogger.getInstance(),
      )
      .first
      .also { assertFalse(it.isInlined, "$filepath must keep its procedure calls") }

  private fun waitlist() =
    PriorityWaitlist.create(
      ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())
    )

  @ParameterizedTest
  @MethodSource("data")
  @Timeout(60, unit = TimeUnit.SECONDS)
  fun testExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    val xcfa = parse(filepath)
    val analysis =
      ExplXcfaAnalysis(
        xcfa,
        Z3LegacySolverFactory.getInstance().createSolver(),
        1,
        getStackPartialOrder(ExplOrd.getInstance().getPtrPartialOrd()),
        false,
      )
    val abstractor =
      getXcfaAbstractor(
        analysis,
        waitlist(),
        StopCriterions.firstCex<XcfaState<PtrState<ExplState>>, XcfaAction>(),
        NullLogger.getInstance(),
        getXcfaLts(Random(1001)),
        getXcfaErrorDetector(property.verifiedProperty, ParseContext()),
      )
        as ArgAbstractor<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>
    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceSeqItpChecker.create(
          True(),
          True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        XcfaPrecRefiner<XcfaState<PtrState<ExplState>>, ExplPrec, ItpRefutation>(
          ItpRefToPtrPrec(ItpRefToExplPrec())
        ),
        PruneStrategy.LAZY,
        NullLogger.getInstance(),
      ) as ArgRefiner<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

    val result =
      ArgCegarChecker.create(abstractor, refiner)
        .check(XcfaPrec(PtrPrec(ExplPrec.empty(), emptySet())))

    assertTrue(verdict(result), "$filepath: $result")
  }

  @ParameterizedTest
  @MethodSource("data")
  @Timeout(60, unit = TimeUnit.SECONDS)
  fun testPredCart(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    val xcfa = parse(filepath)
    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val analysis =
      PredXcfaAnalysis(
        xcfa,
        solver,
        PredAbstractors.cartesianAbstractor(solver),
        getStackPartialOrder(PredOrd.create(solver).getPtrPartialOrd()),
        false,
      )
    val abstractor =
      getXcfaAbstractor(
        analysis,
        waitlist(),
        StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
        NullLogger.getInstance(),
        getXcfaLts(Random(1001)),
        getXcfaErrorDetector(property.verifiedProperty, ParseContext()),
      )
        as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>
    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceBwBinItpChecker.create(
          True(),
          True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        XcfaPrecRefiner<XcfaState<PtrState<PredState>>, PredPrec, ItpRefutation>(
          ItpRefToPtrPrec(ItpRefToPredPrec(ExprSplitters.whole()))
        ),
        PruneStrategy.LAZY,
        NullLogger.getInstance(),
      ) as ArgRefiner<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val result =
      ArgCegarChecker.create(abstractor, refiner)
        .check(XcfaPrec(PtrPrec(PredPrec.of(), emptySet())))

    assertTrue(verdict(result), "$filepath: $result")
  }
}
