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
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStatePredicate
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.multi.stmt.ExprMultiState
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiAction
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiAnalysis
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiLts
import hu.bme.mit.theta.analysis.pred.ExprSplitters
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.CfaAction
import hu.bme.mit.theta.cfa.analysis.CfaAnalysis
import hu.bme.mit.theta.cfa.analysis.CfaPrec
import hu.bme.mit.theta.cfa.analysis.CfaState
import hu.bme.mit.theta.cfa.analysis.lts.CfaLts
import hu.bme.mit.theta.cfa.analysis.lts.CfaSbeLts
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec
import hu.bme.mit.theta.cfa.analysis.prec.RefutationToGlobalCfaPrec
import hu.bme.mit.theta.cfa.copyWithReplacingVars
import hu.bme.mit.theta.cfa.dsl.CfaDslManager
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import org.junit.Test
import org.junit.jupiter.api.Assertions.assertTrue
import java.io.FileInputStream
import java.io.IOException
import java.io.SequenceInputStream

class MultiOfTwoTest {

    val logger: Logger = ConsoleLogger(Logger.Level.SUBSTEP)
    val solver: Solver = Z3SolverFactory.getInstance().createSolver()
    val itpSolver = Z3SolverFactory.getInstance().createItpSolver()

    @Test
    fun testExplPrec() {
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

        val xstsConfigBuilder = XstsConfigBuilder(
            XstsConfigBuilder.Domain.EXPL,
            XstsConfigBuilder.Refinement.SEQ_ITP,
            Z3SolverFactory.getInstance(),
            Z3SolverFactory.getInstance()
        )
        val xstsExplBuilder = xstsConfigBuilder.ExplStrategy(xsts)

        val variables = xsts.vars

        var originalCfa: CFA
        FileInputStream("src/test/resources/cfa/doubler.cfa").use { inputStream ->
            originalCfa = CfaDslManager.createCfa(inputStream)
        }
        val cfa = originalCfa.copyWithReplacingVars(mapOf(*(variables.map { Pair(it.name, it) }.toTypedArray())))
        val dataAnalysis = xstsExplBuilder.dataAnalysis
        val cfaAnalysis = CfaAnalysis.create(cfa.initLoc, dataAnalysis)
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
            .addRightSide(xstsExplBuilder.multiSide, xstsExplBuilder.lts)
            .build<ExplPrec, ExprMultiState<CfaState<UnitState>, XstsState<UnitState>, ExplState>, StmtMultiAction<CfaAction, XstsAction>>(
                NextSideFunctions::alternating,
                dataAnalysis.initFunc,
                { ls, rs, dns, dif -> StmtMultiAnalysis.of(ls, rs, dns, dif) },
                { llts, cls, rlts, crs, dns -> StmtMultiLts.of(llts, cls, rlts, crs, dns) })
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

    @Test
    fun testPredPrec() {
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

        val xstsConfigBuilder = XstsConfigBuilder(
            XstsConfigBuilder.Domain.PRED_BOOL,
            XstsConfigBuilder.Refinement.SEQ_ITP,
            Z3SolverFactory.getInstance(),
            Z3SolverFactory.getInstance()
        )
        val xstsPredBuilder = xstsConfigBuilder.PredStrategy(xsts)
        val dataAnalysis = xstsPredBuilder.dataAnalysis

        var cfa: CFA
        FileInputStream("src/test/resources/cfa/doubler.cfa").use { inputStream ->
            cfa = CfaDslManager.createCfa(inputStream)
        }
        val cfaAnalysis = CfaAnalysis.create(cfa.initLoc, dataAnalysis)
        val cfaLts: CfaLts = CfaSbeLts.getInstance()
        val cfaRefToPrec = RefutationToGlobalCfaPrec(ItpRefToPredPrec(ExprSplitters.atoms()), cfa.initLoc)
        val cfaInitFunc =
            { _: CfaPrec<PredPrec> -> listOf<CfaState<UnitState>>(CfaState.of(cfa.initLoc, UnitState.getInstance())) }
        val dataInitPrec = PredPrec.of()
        val cfaInitPrec: CfaPrec<PredPrec> = GlobalCfaPrec.create(dataInitPrec)
        val cfaCombineStates = { c: CfaState<UnitState>, d: PredState -> CfaState.of(c.loc, d) }
        val cfaStripState = { c: CfaState<PredState> -> CfaState.of(c.loc, UnitState.getInstance()) }
        val cfaExtractFromState = { c: CfaState<PredState> -> c.state }
        val cfaStripPrec = { p: CfaPrec<PredPrec> -> p }

        val product = MultiBuilder.initWithLeftSide(
            cfaAnalysis,
            cfaLts,
            cfaCombineStates,
            cfaStripState,
            cfaExtractFromState,
            cfaInitFunc,
            cfaStripPrec
        )
            .addRightSide(xstsPredBuilder.multiSide, xstsPredBuilder.lts)
            .build<PredPrec, ExprMultiState<CfaState<UnitState>, XstsState<UnitState>, PredState>, StmtMultiAction<CfaAction, XstsAction>>(
                NextSideFunctions::alternating,
                dataAnalysis.initFunc,
                { ls, rs, dns, dif -> StmtMultiAnalysis.of(ls, rs, dns, dif) },
                { llts, cls, rlts, crs, dns -> StmtMultiLts.of(llts, cls, rlts, crs, dns) })
        val prop = Not(xsts.prop)
        val dataPredicate = ExprStatePredicate(prop, solver)
        val argBuilder = ArgBuilder.create(product.lts, product.analysis) { s -> dataPredicate.test(s.dataState) }
        val abstractor = BasicAbstractor.builder(argBuilder).build()
        val traceChecker = ExprTraceSeqItpChecker.create(True(), prop, itpSolver)
        val precRefiner =
            JoiningPrecRefiner.create<ExprMultiState<CfaState<UnitState>, XstsState<UnitState>, PredState>, StmtMultiAction<CfaAction, XstsAction>, MultiPrec<CfaPrec<PredPrec>?, PredPrec, PredPrec>, ItpRefutation>(
                RefToMultiPrec(
                    cfaRefToPrec, ItpRefToPredPrec(ExprSplitters.atoms()),
                    ItpRefToPredPrec(ExprSplitters.atoms())
                )
            )
        val refiner = SingleExprTraceRefiner.create(traceChecker, precRefiner, PruneStrategy.FULL, logger)
        val checker = CegarChecker.create(abstractor, refiner)

        val result = checker.check(MultiPrec(cfaInitPrec, dataInitPrec, dataInitPrec))

        assertTrue(result.isUnsafe)
    }

}