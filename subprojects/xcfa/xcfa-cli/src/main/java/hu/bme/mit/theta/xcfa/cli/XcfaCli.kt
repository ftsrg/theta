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
package hu.bme.mit.theta.xcfa.cli

import com.beust.jcommander.JCommander
import com.beust.jcommander.Parameter
import com.beust.jcommander.ParameterException
import hu.bme.mit.theta.analysis.Analysis
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc
import hu.bme.mit.theta.analysis.expl.ExplTransFunc
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.io.File
import java.io.FileInputStream
import java.util.*
import java.util.ArrayDeque

class XcfaCli(private val args: Array<String>) {
    //////////// CONFIGURATION OPTIONS BEGIN ////////////
    //////////// input task ////////////
    @Parameter(names = ["--input"], description = "Path of the input C program", required = true)
    var input: File? = null
    private fun run() {
        /// Checking flags
        try {
            JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(*args)
        } catch (ex: ParameterException) {
            println("Invalid parameters, details:")
            println(ex.message)
            ex.usage()
            return
        }

        val stream = FileInputStream(input!!)
        val xcfa = getXcfaFromC(stream)

        val initLocStack: Deque<XcfaLocation> = ArrayDeque()
        initLocStack.add(xcfa.initProcedures[0].first.initLoc)

        val initState = XcfaState(mapOf(Pair(0, XcfaProcessState(initLocStack))), ExplState.top())

        val explTransFunc = ExplStmtTransFunc.create(Z3SolverFactory.getInstance().createSolver(), 1)

        val analysis: Analysis<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> = XcfaAnalysis(
                { s1, s2 -> s1.processes == s2.processes && s1.sGlobal.isLeq(s2.sGlobal)},
                { p -> listOf(initState) },
                { s, a, p ->
                    val newSt = s.applyLoc(a)
                    explTransFunc.getSuccStates(newSt.sGlobal, a, p.p).map { newSt.withState(it) }
                }
        )
        val argBuilder: ArgBuilder<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> = ArgBuilder.create(
                { s: XcfaState<ExplState> -> s.processes[0]!!.locs.peek().outgoingEdges.map { XcfaAction(0, it) } },
                analysis,
                { s -> s.processes.any { it.value.locs.peek().error }}
        )

        val logger = ConsoleLogger(Logger.Level.INFO)


        val abstractor: Abstractor<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> =
                BasicAbstractor.builder(argBuilder).projection { s -> s.processes }
                        .waitlist(PriorityWaitlist.create(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())))
                        .stopCriterion(StopCriterions.firstCex()).logger(logger).build()


        val precRefiner: PrecRefiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>, ItpRefutation> = XcfaPrecRefiner(ItpRefToExplPrec())
        val refiner: Refiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> =
                SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(), Z3SolverFactory.getInstance().createItpSolver()),
                        precRefiner, PruneStrategy.LAZY, logger)

        val cegarChecker: CegarChecker<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>> = CegarChecker.create(abstractor, refiner, logger)

        val safetyResult = cegarChecker.check(XcfaPrec(ExplPrec.empty()))

        println(safetyResult)
    }

    companion object {
        private const val JAR_NAME = "theta-xcfa-cli.jar"
        @JvmStatic
        fun main(args: Array<String>) {
            val mainApp = XcfaCli(args)
            mainApp.run()
        }
    }
}