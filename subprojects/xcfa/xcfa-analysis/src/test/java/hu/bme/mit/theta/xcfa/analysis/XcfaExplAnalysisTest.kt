/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expl.*
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.ptr.ItpRefToPtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.getPtrPartialOrd
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.analysis.coi.ConeOfInfluence
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiMultiThread
import hu.bme.mit.theta.xcfa.analysis.por.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.util.*
import kotlin.random.Random


class XcfaExplAnalysisTest {


    companion object {

        private val seed = 1001

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
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testNoporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        println("Testing NOPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false, NullLogger.getInstance()).first
        ConeOfInfluence = XcfaCoiMultiThread(xcfa)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3LegacySolverFactory.getInstance().createSolver(),
            1,
            getPartialOrder(ExplOrd.getInstance().getPtrPartialOrd()), false
        )

        val lts = getXcfaLts()

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<PtrState<ExplState>>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as ArgAbstractor<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val precRefiner = XcfaPrecRefiner<XcfaState<PtrState<ExplState>>, ExplPrec, ItpRefutation>(
            ItpRefToPtrPrec(ItpRefToExplPrec()))

        val refiner =
            XcfaSingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3LegacySolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as ArgRefiner<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val cegarChecker =
            ArgCegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(ExplPrec.empty(), emptySet())))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testSporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        println("Testing SPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false, NullLogger.getInstance()).first
        ConeOfInfluence = XcfaCoiMultiThread(xcfa)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3LegacySolverFactory.getInstance().createSolver(),
            1,
            getPartialOrder(ExplOrd.getInstance().getPtrPartialOrd()), false
        )

        val lts = XcfaSporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<PtrState<ExplState>>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as ArgAbstractor<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val precRefiner = XcfaPrecRefiner<XcfaState<PtrState<ExplState>>, ExplPrec, ItpRefutation>(
            ItpRefToPtrPrec(ItpRefToExplPrec()))

        val refiner =
            XcfaSingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3LegacySolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as ArgRefiner<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val cegarChecker =
            ArgCegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(ExplPrec.empty(), emptySet())))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testDporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        XcfaDporLts.random = Random(seed)
        println("Testing DPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false, NullLogger.getInstance()).first
        ConeOfInfluence = XcfaCoiMultiThread(xcfa)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3LegacySolverFactory.getInstance().createSolver(),
            1,
            XcfaDporLts.getPartialOrder(getPartialOrder(ExplOrd.getInstance().getPtrPartialOrd())), false
        )

        val lts = XcfaDporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            lts.waitlist,
            StopCriterions.firstCex<XcfaState<PtrState<ExplState>>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as ArgAbstractor<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val precRefiner = XcfaPrecRefiner<XcfaState<PtrState<ExplState>>, ExplPrec, ItpRefutation>(
            ItpRefToPtrPrec(ItpRefToExplPrec()))

        val refiner =
            XcfaSingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3LegacySolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                ConsoleLogger(
                    Logger.Level.DETAIL)) as ArgRefiner<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val cegarChecker =
            ArgCegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(ExplPrec.empty(), emptySet())))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testAasporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        println("Testing AASPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false, NullLogger.getInstance()).first
        ConeOfInfluence = XcfaCoiMultiThread(xcfa)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3LegacySolverFactory.getInstance().createSolver(),
            1,
            getPartialOrder(ExplOrd.getInstance().getPtrPartialOrd()), false
        )

        val lts = XcfaAasporLts(xcfa, mutableMapOf())

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<PtrState<ExplState>>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as ArgAbstractor<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val precRefiner = XcfaPrecRefiner<PtrState<ExplState>, ExplPrec, ItpRefutation>(
            ItpRefToPtrPrec(ItpRefToExplPrec()))
        val atomicNodePruner = AtomicNodePruner<XcfaState<PtrState<ExplState>>, XcfaAction>()

        val refiner =
            XcfaSingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3LegacySolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL, NullLogger.getInstance(),
                atomicNodePruner) as ArgRefiner<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val cegarChecker =
            ArgCegarChecker.create(abstractor, AasporRefiner.create(refiner, PruneStrategy.FULL, mutableMapOf()))

        val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(ExplPrec.empty(), emptySet())))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testAadporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        XcfaDporLts.random = Random(seed)
        println("Testing AADPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false, NullLogger.getInstance()).first
        ConeOfInfluence = XcfaCoiMultiThread(xcfa)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3LegacySolverFactory.getInstance().createSolver(),
            1,
            XcfaDporLts.getPartialOrder(getPartialOrder(ExplOrd.getInstance().getPtrPartialOrd())), false
        )

        val lts = XcfaAadporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            lts.waitlist,
            StopCriterions.firstCex<XcfaState<PtrState<ExplState>>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as ArgAbstractor<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val precRefiner = XcfaPrecRefiner<ExplState, ExplPrec, ItpRefutation>(ItpRefToPtrPrec(ItpRefToExplPrec()))

        val refiner =
            XcfaSingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3LegacySolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as ArgRefiner<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

        val cegarChecker =
            ArgCegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(PtrPrec(ExplPrec.empty(), emptySet())))



        Assertions.assertTrue(verdict(safetyResult))
    }
}