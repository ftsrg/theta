/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.analysis.por.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.util.*
import kotlin.random.Random


class XcfaPredAnalysisTest {


    companion object {

        private val seed = 1001;

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
    fun testNoporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        println("Testing NOPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false).first

        val solver = Z3SolverFactory.getInstance().createSolver()
        val analysis = PredXcfaAnalysis(
            xcfa,
            solver,
            PredAbstractors.cartesianAbstractor(solver),
            getPartialOrder(PredOrd.create(solver))
        )

        val lts = getXcfaLts()

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<PredState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val precRefiner = XcfaPrecRefiner<XcfaState<PredState>, PredPrec, ItpRefutation>(
            ItpRefToPredPrec(ExprSplitters.whole()))

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as Refiner<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(PredPrec.of()))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testSporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        println("Testing SPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false).first

        val solver = Z3SolverFactory.getInstance().createSolver()
        val analysis = PredXcfaAnalysis(
            xcfa,
            solver,
            PredAbstractors.cartesianAbstractor(solver),
            getPartialOrder(PredOrd.create(solver))
        )

        val lts = XcfaSporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<PredState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val precRefiner = XcfaPrecRefiner<XcfaState<PredState>, PredPrec, ItpRefutation>(
            ItpRefToPredPrec(ExprSplitters.whole()))

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as Refiner<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(PredPrec.of()))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testDporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        XcfaDporLts.random = Random(seed)
        println("Testing DPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false).first

        val solver = Z3SolverFactory.getInstance().createSolver()
        val analysis = PredXcfaAnalysis(
            xcfa,
            solver,
            PredAbstractors.cartesianAbstractor(solver),
            XcfaDporLts.getPartialOrder(getPartialOrder(PredOrd.create(solver)))
        )

        val lts = XcfaDporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            lts.waitlist,
            StopCriterions.firstCex<XcfaState<PredState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val precRefiner = XcfaPrecRefiner<XcfaState<PredState>, PredPrec, ItpRefutation>(
            ItpRefToPredPrec(ExprSplitters.whole()))

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                ConsoleLogger(Logger.Level.DETAIL)) as Refiner<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(PredPrec.of()))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testAasporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        println("Testing AASPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false).first

        val solver = Z3SolverFactory.getInstance().createSolver()
        val analysis = PredXcfaAnalysis(
            xcfa,
            solver,
            PredAbstractors.cartesianAbstractor(solver),
            getPartialOrder(PredOrd.create(solver))
        )

        val lts = XcfaAasporLts(xcfa, mutableMapOf())

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<PredState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val precRefiner = XcfaPrecRefiner<PredState, PredPrec, ItpRefutation>(ItpRefToPredPrec(ExprSplitters.whole()))
        val atomicNodePruner = AtomicNodePruner<XcfaState<PredState>, XcfaAction>()

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL, NullLogger.getInstance(),
                atomicNodePruner) as Refiner<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, AasporRefiner.create(refiner, PruneStrategy.FULL, mutableMapOf()))

        val safetyResult = cegarChecker.check(XcfaPrec(PredPrec.of()))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testAadporPred(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        XcfaDporLts.random = Random(seed)
        println("Testing AADPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false).first

        val solver = Z3SolverFactory.getInstance().createSolver()
        val analysis = PredXcfaAnalysis(
            xcfa,
            solver,
            PredAbstractors.cartesianAbstractor(solver),
            XcfaDporLts.getPartialOrder(getPartialOrder(PredOrd.create(solver)))
        )

        val lts = XcfaAadporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            lts.waitlist,
            StopCriterions.firstCex<XcfaState<PredState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val precRefiner = XcfaPrecRefiner<PredState, PredPrec, ItpRefutation>(ItpRefToPredPrec(ExprSplitters.whole()))

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as Refiner<XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(PredPrec.of()))



        Assertions.assertTrue(verdict(safetyResult))
    }
}