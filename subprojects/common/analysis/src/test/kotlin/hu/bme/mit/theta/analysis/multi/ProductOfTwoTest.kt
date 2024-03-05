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
package hu.bme.mit.theta.analysis.multi

import hu.bme.mit.theta.analysis.algorithm.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.expl.*
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.stmtoptimizer.DefaultStmtOptimizer
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.CfaAction
import hu.bme.mit.theta.cfa.analysis.CfaAnalysis.create
import hu.bme.mit.theta.cfa.analysis.CfaPrec
import hu.bme.mit.theta.cfa.analysis.CfaState
import hu.bme.mit.theta.cfa.analysis.lts.CfaLts
import hu.bme.mit.theta.cfa.analysis.lts.CfaSbeLts
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec
import hu.bme.mit.theta.cfa.analysis.prec.RefutationToGlobalCfaPrec
import hu.bme.mit.theta.cfa.dsl.CfaDslManager
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.*
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import org.junit.Test
import org.junit.jupiter.api.Assertions.assertTrue
import java.io.FileInputStream
import java.io.IOException
import java.io.SequenceInputStream

class ProductOfTwoTest {

    val logger: Logger = ConsoleLogger(Logger.Level.SUBSTEP)
    val solver: Solver = Z3SolverFactory.getInstance().createSolver()
    val itpSolver = Z3SolverFactory.getInstance().createItpSolver()

    @Test
    fun test() {
        var xsts: XSTS
        try {
            SequenceInputStream(
                FileInputStream("src/test/resources/xsts/incrementor.xsts"),
                FileInputStream("src/test/resources/xsts/xneq7.prop")
            ).use { inputStream ->
                xsts = XstsDslManager.createXsts(inputStream)
            }
        } catch (e: IOException) {
            throw RuntimeException(e)
        }
        val dataAnalysis = ExplAnalysis.create(
            solver,
            xsts.initFormula
        )
        val xstsAnalysis = XstsAnalysis.create(dataAnalysis)
        val xstsLts = XstsLts.create(xsts, XstsStmtOptimizer.create(DefaultStmtOptimizer.create<ExplState>()))
        val xstsInitFunc = XstsInitFunc.create { _: ExplPrec -> listOf<UnitState>(UnitState.getInstance()) }
        val xstsCombineStates = { x: XstsState<UnitState>, d: ExplState -> XstsState.of(d, x.lastActionWasEnv(), true) }
        val xstsStripState =
            { x: XstsState<ExplState> -> XstsState.of(UnitState.getInstance(), x.lastActionWasEnv(), true) }
        val xstsExtractFromState = { x: XstsState<ExplState> -> x.state }
        val xstsStripPrec = { p: ExplPrec -> p }
        val variables = xsts.vars

        var cfa: CFA
        FileInputStream("src/test/resources/cfa/doubler.cfa").use { inputStream ->
            cfa = CfaDslManager.createCfa(inputStream)
        }
        val cfaAnalysis = create(cfa.initLoc, dataAnalysis)
        val cfaLts: CfaLts = CfaSbeLts.getInstance()
        val cfaRefToPrec = RefutationToGlobalCfaPrec(ItpRefToExplPrec(), cfa.initLoc)
        val cfaInitFunc =
            { _: CfaPrec<ExplPrec> -> listOf<CfaState<UnitState>>(CfaState.of(cfa.initLoc, UnitState.getInstance())) }
        val dataInitPrec = ExplPrec.of(variables)
        val cfaInitPrec: CfaPrec<ExplPrec> = GlobalCfaPrec.create(dataInitPrec)
        val cfaCombineStates = { c: CfaState<UnitState>, d: ExplState -> CfaState.of(c.loc, d) }
        val cfaStripState = { c: CfaState<ExplState> -> CfaState.of(c.loc, UnitState.getInstance()) }
        val cfaExtractFromState = { c: CfaState<ExplState> -> c.state }
        val cfaStripPrec = { p: CfaPrec<ExplPrec> -> p }


        val product = MultiBuilder.initWithLeftSide(
            cfaAnalysis,
            cfaLts,
            cfaCombineStates,
            cfaStripState,
            cfaExtractFromState,
            cfaInitFunc,
            cfaStripPrec
        )
            .addRightSide(
                xstsAnalysis,
                xstsLts,
                xstsCombineStates,
                xstsStripState,
                xstsExtractFromState,
                xstsInitFunc,
                xstsStripPrec
            )
            .build<ExplPrec, ExprMultiState<CfaState<UnitState>, XstsState<UnitState>, ExplState>, StmtMultiAction<CfaAction, XstsAction>>(
                NextSideFunctions::alternating,
                dataAnalysis.initFunc,
                { ls, rs, dns, dif -> ExprMultiAnalysis.of(ls, rs, dns, dif) },
                { llts, cls, rlts, crs, dns -> ExprMultiLts.of(llts, cls, rlts, crs, dns) })
        val prop = Not(xsts.prop)
        val dataPredicate = ExplStatePredicate(prop, solver)
        val argBuilder = ArgBuilder.create(product.lts, product.analysis) { s -> dataPredicate.test(s.dataState) }
        val abstractor = BasicAbstractor.builder(argBuilder).build()
        val traceChecker = ExprTraceSeqItpChecker.create(True(), prop, itpSolver)
        val precRefiner =
            JoiningPrecRefiner.create<ExprMultiState<CfaState<UnitState>, XstsState<UnitState>, ExplState>, StmtMultiAction<CfaAction, XstsAction>, MultiPrec<CfaPrec<ExplPrec>?, ExplPrec, ExplPrec>, ItpRefutation>(
                RefToMultiPrec(cfaRefToPrec, ItpRefToExplPrec(), ItpRefToExplPrec())
            )
        val refiner = SingleExprTraceRefiner.create(traceChecker, precRefiner, PruneStrategy.FULL, logger)
        val checker = CegarChecker.create(abstractor, refiner)
        val result = checker.check(MultiPrec(cfaInitPrec, dataInitPrec, dataInitPrec))
        assertTrue(result.isUnsafe)
    }

}