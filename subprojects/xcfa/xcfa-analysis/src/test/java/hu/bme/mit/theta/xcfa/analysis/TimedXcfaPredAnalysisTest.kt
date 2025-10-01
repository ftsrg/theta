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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expr.refinement.*
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
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.analysis.coi.ConeOfInfluence
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiMultiThread
import hu.bme.mit.theta.xcfa.analysis.por.*
import java.util.*
import kotlin.random.Random
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class TimedXcfaPredAnalysisTest {

    companion object {

        @JvmStatic
        fun data(): Collection<Array<Any>> {
            return listOf(
                arrayOf("/05multithreadtimed.c", ExprSplitters.whole(), SafetyResult<*, *>::isSafe),
                arrayOf("/05multithreadtimed.c", ExprSplitters.atoms(), SafetyResult<*, *>::isSafe),
            )
        }
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testRatClocks(filepath: String, exprSplitter : ExprSplitters.ExprSplitter, verdict: (SafetyResult<*, *>) -> Boolean) {
        println("Testing NOPOR on $filepath...")
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false, NullLogger.getInstance()).first
        ConeOfInfluence = XcfaCoiMultiThread(xcfa)

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

        val abstractor =
            getXcfaAbstractor(
                analysis,
                PriorityWaitlist.create(
                    ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())
                ),
                StopCriterions.firstCex<XcfaState<PtrState<PredState>>, XcfaAction>(),
                ConsoleLogger(Logger.Level.DETAIL),
                lts,
                ErrorDetection.ERROR_LOCATION,
            )
                as ArgAbstractor<XcfaState<PtrState<PredState>>, XcfaAction, XcfaPrec<PtrPrec<PredPrec>>>

        val precRefiner =
            XcfaPrecRefiner<XcfaState<PtrState<PredState>>, PredPrec, ItpRefutation>(
                ItpRefToPtrPrec(ItpRefToPredPrec(exprSplitter))
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
}
