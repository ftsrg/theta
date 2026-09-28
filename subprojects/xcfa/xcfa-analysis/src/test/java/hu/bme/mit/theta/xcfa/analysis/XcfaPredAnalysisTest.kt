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
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.AasporRefiner
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.ptr.ItpRefToPtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.getPtrPartialOrd
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.por.*
import hu.bme.mit.theta.xcfa.passes.LbePass
import kotlin.random.Random
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class XcfaPredAnalysisTest {

  private val parseContext = ParseContext()

  companion object {

    private val seed = 1001

    private val property = XcfaProperty(ErrorDetection.ERROR_LOCATION)
    private val assertionProperty = XcfaProperty(ErrorDetection.NO_ASSERTION_VIOLATION)

    @JvmStatic
    fun data(): Collection<Array<Any>> {
      return listOf(
        arrayOf("/00assignment.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/01function.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/02functionparam.c", SafetyResult<*, *>::isSafe),
        arrayOf("/03nondetfunction.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/04multithread.c", SafetyResult<*, *>::isUnsafe),
      )
    }

    @JvmStatic
    fun assertionData(): Collection<Array<Any>> {
      return listOf(
        arrayOf("/08assert.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/09assert_safe.c", SafetyResult<*, *>::isSafe),
      )
    }
  }

  fun testNoporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    println("Testing NOPOR on $filepath...")
    val stream = javaClass.getResourceAsStream(filepath)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val analysis =
      PredXcfaAnalysis(
        xcfa,
        solver,
        PredAbstractors.cartesianAbstractor(solver),
        getPartialOrder(PredOrd.create(solver).getPtrPartialOrd()),
        false,
      )

    val lts = getXcfaLts()

    val errorDetector = getXcfaErrorDetector(property.verifiedProperty, parseContext)
    val abstractor =
      getXcfaAbstractor(
        analysis,
        PriorityWaitlist.create(
          ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())
        ),
        StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
        ConsoleLogger(Logger.Level.DETAIL),
        lts,
        errorDetector,
      )
        as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val precRefiner =
      XcfaPrecRefiner<XcfaState<PtrState<PredState>>, PredPrec, ItpRefutation>(
        ItpRefToPtrPrec(ItpRefToPredPrec(ExprSplitters.whole()))
      )

    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceBwBinItpChecker.create(
          BoolExprs.True(),
          BoolExprs.True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        precRefiner,
        PruneStrategy.FULL,
        NullLogger.getInstance(),
      ) as ArgRefiner<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val cegarChecker = ArgCegarChecker.create(abstractor, refiner)

    val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(PredPrec.of(), emptySet())))

    Assertions.assertTrue(verdict(safetyResult))
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testSporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    println("Testing SPOR on $filepath...")
    val stream = javaClass.getResourceAsStream(filepath)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val analysis =
      PredXcfaAnalysis(
        xcfa,
        solver,
        PredAbstractors.cartesianAbstractor(solver),
        getPartialOrder(PredOrd.create(solver).getPtrPartialOrd()),
        false,
      )

    val lts = XcfaSporLts(xcfa)

    val errorDetector = getXcfaErrorDetector(property.verifiedProperty, parseContext)
    val abstractor =
      getXcfaAbstractor(
        analysis,
        PriorityWaitlist.create(
          ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())
        ),
        StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
        ConsoleLogger(Logger.Level.DETAIL),
        lts,
        errorDetector,
      )
        as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val precRefiner =
      XcfaPrecRefiner<XcfaState<PtrState<PredState>>, PredPrec, ItpRefutation>(
        ItpRefToPtrPrec(ItpRefToPredPrec(ExprSplitters.whole()))
      )

    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceBwBinItpChecker.create(
          BoolExprs.True(),
          BoolExprs.True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        precRefiner,
        PruneStrategy.FULL,
        NullLogger.getInstance(),
      ) as ArgRefiner<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val cegarChecker = ArgCegarChecker.create(abstractor, refiner)

    val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(PredPrec.of(), emptySet())))

    Assertions.assertTrue(verdict(safetyResult))
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testDporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    XcfaDporLts.random = Random(seed)
    println("Testing DPOR on $filepath...")
    val stream = javaClass.getResourceAsStream(filepath)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val analysis =
      PredXcfaAnalysis(
        xcfa,
        solver,
        PredAbstractors.cartesianAbstractor(solver),
        XcfaDporLts.getPartialOrder(getPartialOrder(PredOrd.create(solver).getPtrPartialOrd())),
        false,
      )

    val lts = XcfaDporLts(xcfa)

    val errorDetector = getXcfaErrorDetector(property.verifiedProperty, parseContext)
    val abstractor =
      getXcfaAbstractor(
        analysis,
        lts.waitlist,
        StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
        ConsoleLogger(Logger.Level.DETAIL),
        lts,
        errorDetector,
      )
        as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val precRefiner =
      XcfaPrecRefiner<XcfaState<PtrState<PredState>>, PredPrec, ItpRefutation>(
        ItpRefToPtrPrec(ItpRefToPredPrec(ExprSplitters.whole()))
      )

    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceBwBinItpChecker.create(
          BoolExprs.True(),
          BoolExprs.True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        precRefiner,
        PruneStrategy.FULL,
        ConsoleLogger(Logger.Level.DETAIL),
      ) as ArgRefiner<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val cegarChecker = ArgCegarChecker.create(abstractor, refiner)

    val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(PredPrec.of(), emptySet())))

    Assertions.assertTrue(verdict(safetyResult))
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testAasporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    println("Testing AASPOR on $filepath...")
    val stream = javaClass.getResourceAsStream(filepath)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val analysis =
      PredXcfaAnalysis(
        xcfa,
        solver,
        PredAbstractors.cartesianAbstractor(solver),
        getPartialOrder(PredOrd.create(solver).getPtrPartialOrd()),
        false,
      )

    val lts = XcfaAasporLts(xcfa, mutableMapOf())

    val errorDetector = getXcfaErrorDetector(property.verifiedProperty, parseContext)
    val abstractor =
      getXcfaAbstractor(
        analysis,
        PriorityWaitlist.create(
          ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())
        ),
        StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
        ConsoleLogger(Logger.Level.DETAIL),
        lts,
        errorDetector,
      )
        as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val precRefiner =
      XcfaPrecRefiner<PtrState<PredState>, PredPrec, ItpRefutation>(
        ItpRefToPtrPrec(ItpRefToPredPrec(ExprSplitters.whole()))
      )
    val atomicNodePruner = AtomicNodePruner<XcfaState<PtrState<PredState>>, XcfaAction>()

    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceBwBinItpChecker.create(
          BoolExprs.True(),
          BoolExprs.True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        precRefiner,
        PruneStrategy.FULL,
        NullLogger.getInstance(),
        atomicNodePruner,
      ) as ArgRefiner<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val cegarChecker =
      ArgCegarChecker.create(
        abstractor,
        AasporRefiner.create(refiner, PruneStrategy.FULL, mutableMapOf()),
      )

    val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(PredPrec.of(), emptySet())))

    Assertions.assertTrue(verdict(safetyResult))
  }

  fun testAadporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    XcfaDporLts.random = Random(seed)
    println("Testing AADPOR on $filepath...")
    val stream = javaClass.getResourceAsStream(filepath)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val analysis =
      PredXcfaAnalysis(
        xcfa,
        solver,
        PredAbstractors.cartesianAbstractor(solver),
        XcfaDporLts.getPartialOrder(getPartialOrder(PredOrd.create(solver).getPtrPartialOrd())),
        false,
      )

    val lts = XcfaAadporLts(xcfa)

    val errorDetector = getXcfaErrorDetector(property.verifiedProperty, parseContext)
    val abstractor =
      getXcfaAbstractor(
        analysis,
        lts.waitlist,
        StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
        ConsoleLogger(Logger.Level.DETAIL),
        lts,
        errorDetector,
      )
        as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val precRefiner =
      XcfaPrecRefiner<PredState, PredPrec, ItpRefutation>(
        ItpRefToPtrPrec(ItpRefToPredPrec(ExprSplitters.whole()))
      )

    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceBwBinItpChecker.create(
          BoolExprs.True(),
          BoolExprs.True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        precRefiner,
        PruneStrategy.FULL,
        NullLogger.getInstance(),
      ) as ArgRefiner<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val cegarChecker = ArgCegarChecker.create(abstractor, refiner)

    val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(PredPrec.of(), emptySet())))

    Assertions.assertTrue(verdict(safetyResult))
  }

  @ParameterizedTest
  @MethodSource("assertionData")
  fun testSporPredAssertions(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    println("Testing assertion SPOR on $filepath...")
    val stream = javaClass.getResourceAsStream(filepath)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, assertionProperty, NullLogger.getInstance())
        .first

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val analysis =
      PredXcfaAnalysis(
        xcfa,
        solver,
        PredAbstractors.cartesianAbstractor(solver),
        getPartialOrder(PredOrd.create(solver).getPtrPartialOrd()),
        false,
      )

    val lts = XcfaSporLts(xcfa)

    val errorDetector = getXcfaErrorDetector(assertionProperty.verifiedProperty, parseContext)
    val abstractor =
      getXcfaAbstractor(
        analysis,
        PriorityWaitlist.create(
          ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())
        ),
        StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
        ConsoleLogger(Logger.Level.DETAIL),
        lts,
        errorDetector,
      )
        as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val precRefiner =
      XcfaPrecRefiner<XcfaState<PtrState<PredState>>, PredPrec, ItpRefutation>(
        ItpRefToPtrPrec(ItpRefToPredPrec(ExprSplitters.whole()))
      )

    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceBwBinItpChecker.create(
          BoolExprs.True(),
          BoolExprs.True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        precRefiner,
        PruneStrategy.FULL,
        NullLogger.getInstance(),
      ) as ArgRefiner<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val cegarChecker = ArgCegarChecker.create(abstractor, refiner)

    val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(PredPrec.of(), emptySet())))

    Assertions.assertTrue(verdict(safetyResult))
  }

  /**
   * Split abstraction can give one action several successors; lazy pruning may remove only some of
   * them, and AASPOR must still re-fire that action (issue #267).
   */
  @Test
  fun testAasporPredSplitLazyPruning() {
    val stream = javaClass.getResourceAsStream("/13nondetsum.c")
    // The CLI's default LBE level; without it the pruned split successor is not hit.
    val lbeLevel = LbePass.defaultLevel
    LbePass.defaultLevel = LbePass.LbeLevel.LBE_SEQ
    val xcfa =
      try {
        getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first
      } finally {
        LbePass.defaultLevel = lbeLevel
      }

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val analysis =
      PredXcfaAnalysis(
        xcfa,
        solver,
        PredAbstractors.booleanSplitAbstractor(solver),
        getPartialOrder(PredOrd.create(solver).getPtrPartialOrd()),
        false,
      )

    val ignoredVarRegistry = mutableMapOf<VarDecl<*>, MutableSet<ExprState>>()
    val lts = XcfaAasporLts(xcfa, ignoredVarRegistry)

    val errorDetector = getXcfaErrorDetector(property.verifiedProperty, parseContext)
    val abstractor =
      getXcfaAbstractor(
        analysis,
        PriorityWaitlist.create(
          ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())
        ),
        StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
        NullLogger.getInstance(),
        lts,
        errorDetector,
      )
        as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val precRefiner =
      XcfaPrecRefiner<PtrState<PredState>, PredPrec, ItpRefutation>(
        ItpRefToPtrPrec(ItpRefToPredPrec(ExprSplitters.whole()))
      )

    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceSeqItpChecker.create(
          BoolExprs.True(),
          BoolExprs.True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        precRefiner,
        PruneStrategy.LAZY,
        NullLogger.getInstance(),
        AtomicNodePruner<XcfaState<PtrState<PredState>>, XcfaAction>(),
      ) as ArgRefiner<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

    val cegarChecker =
      ArgCegarChecker.create(
        abstractor,
        AasporRefiner.create(
          refiner,
          PruneStrategy.LAZY,
          ignoredVarRegistry as MutableMap<VarDecl<*>, MutableSet<XcfaState<PtrState<PredState>>>>,
        ),
      )

    val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(PredPrec.of(), emptySet())))

    Assertions.assertTrue(safetyResult.isUnsafe)
  }
}
