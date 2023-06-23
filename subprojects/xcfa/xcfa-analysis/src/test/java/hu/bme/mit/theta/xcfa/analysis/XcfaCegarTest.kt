/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.Analysis
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplTransFunc
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameter
import java.util.*


@RunWith(Parameterized::class)
class XcfaCegarTest {
    @Parameter(0)
    lateinit var filepath: String
    @Parameter(1)
    lateinit var verdict: (SafetyResult<*, *>) -> Boolean

    companion object {
        @JvmStatic
        @Parameterized.Parameters
        fun data(): Collection<Array<Any>> {
            return listOf(
                    arrayOf("/00assignment.c", SafetyResult<*,*>::isUnsafe),
                    arrayOf("/01function.c", SafetyResult<*,*>::isUnsafe),
                    arrayOf("/02functionparam.c", SafetyResult<*,*>::isSafe),
                    arrayOf("/03nondetfunction.c", SafetyResult<*,*>::isUnsafe),
            )
        }
    }

    @Test
    fun check() {
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, false)

//        System.err.println(xcfa.toDot())

        val initLocStack: LinkedList<XcfaLocation> = LinkedList()
        initLocStack.add(xcfa.initProcedures[0].first.initLoc)

        val initState = XcfaState(xcfa, mapOf(Pair(0, XcfaProcessState(initLocStack, LinkedList()))), ExplState.top())

        val explTransFunc = ExplTransFunc.create(Z3SolverFactory.getInstance().createSolver())

        val analysis: Analysis<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> = XcfaAnalysis(
                { s1, s2 -> s1.processes == s2.processes && s1.sGlobal.isLeq(s2.sGlobal)},
                { p -> listOf(initState) },
                { s, a, p ->
                    val (newSt, newA) = s.apply(a)
                    explTransFunc.getSuccStates(newSt.sGlobal, newA, p.p).map { newSt.withState(it) }
                }
        )
        val argBuilder: ArgBuilder<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> = ArgBuilder.create(
                { s: XcfaState<ExplState> -> s.processes[0]?.locs?.peek()?.outgoingEdges?.map { XcfaAction(0, it) } ?: listOf() },
                analysis,
                { s -> s.processes.any { it.value.locs.peek().error }}
        )


        val abstractor: Abstractor<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> =
                BasicAbstractor.builder(argBuilder).projection { s -> s.processes }
                    .waitlist(PriorityWaitlist.create(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())))
                    .stopCriterion(StopCriterions.firstCex()).logger(NullLogger.getInstance()).build()


        val precRefiner: PrecRefiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>, ItpRefutation> = XcfaPrecRefiner(ItpRefToExplPrec())
        val refiner: Refiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> =
                SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(), Z3SolverFactory.getInstance().createItpSolver()),
                        precRefiner, PruneStrategy.LAZY, NullLogger.getInstance())

        val cegarChecker: CegarChecker<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> = CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(ExplPrec.empty()))

//        val g = ArgVisualizer.getDefault().visualize(safetyResult.arg)
//        println(GraphvizWriter.getInstance().writeString(g))

        Assert.assertTrue(verdict(safetyResult))
    }
}