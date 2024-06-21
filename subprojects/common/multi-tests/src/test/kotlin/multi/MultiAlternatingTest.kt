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
package multi

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplStatePredicate
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate
import hu.bme.mit.theta.analysis.multi.MultiStatePredicate
import hu.bme.mit.theta.analysis.multi.NextSideFunctions
import hu.bme.mit.theta.analysis.multi.builder.stmt.StmtMultiBuilder
import hu.bme.mit.theta.analysis.multi.config.StmtMultiConfigBuilder
import hu.bme.mit.theta.analysis.pred.ExprSplitters
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.CfaPrec
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec
import hu.bme.mit.theta.cfa.analysis.prec.RefutationToGlobalCfaPrec
import hu.bme.mit.theta.cfa.copyWithReplacingVars
import hu.bme.mit.theta.cfa.dsl.CfaDslManager
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import org.junit.Test
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import java.io.FileInputStream
import java.io.IOException
import java.io.SequenceInputStream

class MultiAlternatingTest {

    val logger: Logger = ConsoleLogger(Logger.Level.SUBSTEP)
    val solver: Solver = Z3LegacySolverFactory.getInstance().createSolver()

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
            Z3LegacySolverFactory.getInstance(),
            Z3LegacySolverFactory.getInstance()
        )
        val xstsExplBuilder = xstsConfigBuilder.ExplStrategy(xsts)

        val variables = xsts.vars

        var originalCfa: CFA
        FileInputStream("src/test/resources/cfa/doubler.cfa").use { inputStream ->
            originalCfa = CfaDslManager.createCfa(inputStream)
        }
        val cfa = originalCfa.copyWithReplacingVars(variables.associateBy { it.name })
        val cfaConfigBuilder = CfaConfigBuilder(
            CfaConfigBuilder.Domain.EXPL, CfaConfigBuilder.Refinement.SEQ_ITP,
            Z3LegacySolverFactory.getInstance()
        )
        cfaConfigBuilder.encoding(CfaConfigBuilder.Encoding.SBE)
        val cfaExplBuilder = cfaConfigBuilder.ExplStrategy(cfa)

        val dataAnalysis = xstsExplBuilder.dataAnalysis
        val cfaRefToPrec = RefutationToGlobalCfaPrec(ItpRefToExplPrec(), cfa.initLoc)
        val dataInitPrec = ExplPrec.of(variables)
        val cfaInitPrec: CfaPrec<ExplPrec> = GlobalCfaPrec.create(dataInitPrec)
        val product = StmtMultiBuilder(cfaExplBuilder.multiSide, cfaExplBuilder.lts).addRightSide(
            xstsExplBuilder.multiSide, xstsExplBuilder.lts
        ).build(NextSideFunctions.Alternating(), dataAnalysis.initFunc)
        val prop = Not(xsts.prop)
        val dataPredicate = ExplStatePredicate(prop, solver)
        val multiConfigBuilder = StmtMultiConfigBuilder.ItpStmtMultiConfigBuilder(
            product, prop,
            MultiStatePredicate(dataPredicate),
            cfaRefToPrec, ItpRefToExplPrec(), ItpRefToExplPrec(), cfaInitPrec,
            dataInitPrec, dataInitPrec, Z3LegacySolverFactory.getInstance(), logger
        )
        val result = multiConfigBuilder.build().check()

        assertTrue(result.isUnsafe)
        assertEquals(8, result.asUnsafe().trace.length())
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
            Z3LegacySolverFactory.getInstance(),
            Z3LegacySolverFactory.getInstance()
        )
        val xstsPredBuilder = xstsConfigBuilder.PredStrategy(xsts)
        val dataAnalysis = xstsPredBuilder.dataAnalysis

        var cfa: CFA
        FileInputStream("src/test/resources/cfa/doubler.cfa").use { inputStream ->
            cfa = CfaDslManager.createCfa(inputStream)
        }
        cfa = cfa.copyWithReplacingVars(xsts.vars.associateBy { it.name })
        val cfaConfigBuilder = CfaConfigBuilder(
            CfaConfigBuilder.Domain.PRED_BOOL,
            CfaConfigBuilder.Refinement.SEQ_ITP,
            Z3LegacySolverFactory.getInstance()
        )
        cfaConfigBuilder.encoding(CfaConfigBuilder.Encoding.SBE)
        val cfaPredBuilder = cfaConfigBuilder.PredStrategy(cfa)
        val cfaRefToPrec = RefutationToGlobalCfaPrec(ItpRefToPredPrec(ExprSplitters.atoms()), cfa.initLoc)
        val dataInitPrec = PredPrec.of()
        val cfaInitPrec: CfaPrec<PredPrec> = GlobalCfaPrec.create(dataInitPrec)

        val product = StmtMultiBuilder(cfaPredBuilder.multiSide, cfaPredBuilder.lts)
            .addRightSide(xstsPredBuilder.multiSide, xstsPredBuilder.lts)
            .build(
                NextSideFunctions.Alternating(),
                dataAnalysis.initFunc
            )
        val prop = Not(xsts.prop)
        val dataPredicate = ExprStatePredicate(prop, solver)

        val multiConfigBuilder = StmtMultiConfigBuilder.ItpStmtMultiConfigBuilder(
            product, prop,
            MultiStatePredicate(dataPredicate),
            cfaRefToPrec, ItpRefToPredPrec(ExprSplitters.atoms()), ItpRefToPredPrec(ExprSplitters.atoms()), cfaInitPrec,
            dataInitPrec, dataInitPrec, Z3LegacySolverFactory.getInstance(), logger
        )
        val result = multiConfigBuilder.build().check()

        assertTrue(result.isUnsafe)
    }

}