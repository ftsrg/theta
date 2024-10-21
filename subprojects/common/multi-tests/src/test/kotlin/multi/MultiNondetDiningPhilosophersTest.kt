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

import hu.bme.mit.theta.analysis.expl.ExplInitFunc
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplStatePredicate
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.multi.MultiPrec
import hu.bme.mit.theta.analysis.multi.MultiStatePredicate
import hu.bme.mit.theta.analysis.multi.NextSideFunctions
import hu.bme.mit.theta.analysis.multi.RefToMultiPrec
import hu.bme.mit.theta.analysis.multi.builder.stmt.StmtMultiBuilder
import hu.bme.mit.theta.analysis.multi.config.StmtMultiConfigBuilder
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.CfaPrec
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec
import hu.bme.mit.theta.cfa.analysis.prec.RefutationToGlobalCfaPrec
import hu.bme.mit.theta.cfa.copyWithReplacingVars
import hu.bme.mit.theta.cfa.dsl.CfaDslManager
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.Test
import org.junit.jupiter.api.Assertions
import java.io.FileInputStream

class MultiNondetDiningPhilosophersTest {

    val logger: Logger = ConsoleLogger(Logger.Level.SUBSTEP)
    val solver: Solver = Z3LegacySolverFactory.getInstance().createSolver()

    @Test
    fun test() {
        var phil1cfa: CFA
        FileInputStream("src/test/resources/cfa/philosopher1.cfa").use { inputStream ->
            phil1cfa = CfaDslManager.createCfa(inputStream)
        }
        var phil2rawCfa: CFA
        FileInputStream("src/test/resources/cfa/philosopher2.cfa").use { inputStream ->
            phil2rawCfa = CfaDslManager.createCfa(inputStream)
        }
        var phil3rawCfa: CFA
        FileInputStream("src/test/resources/cfa/philosopher3.cfa").use { inputStream ->
            phil3rawCfa = CfaDslManager.createCfa(inputStream)
        }
        var phil4rawCfa: CFA
        FileInputStream("src/test/resources/cfa/philosopher4.cfa").use { inputStream ->
            phil4rawCfa = CfaDslManager.createCfa(inputStream)
        }
        val variables = phil1cfa.vars
        val phil2cfa = phil2rawCfa.copyWithReplacingVars(variables.associateBy { it.name })
        val phil3cfa = phil3rawCfa.copyWithReplacingVars(variables.associateBy { it.name })
        val phil4cfa = phil4rawCfa.copyWithReplacingVars(variables.associateBy { it.name })

        val cfa1ConfigBuilder = CfaConfigBuilder(CfaConfigBuilder.Domain.EXPL, CfaConfigBuilder.Refinement.SEQ_ITP,
            Z3LegacySolverFactory.getInstance())
        cfa1ConfigBuilder.encoding(CfaConfigBuilder.Encoding.LBE)
        val cfa1ExplBuilder = cfa1ConfigBuilder.ExplStrategy(phil1cfa)
        val cfa2ConfigBuilder = CfaConfigBuilder(CfaConfigBuilder.Domain.EXPL, CfaConfigBuilder.Refinement.SEQ_ITP,
            Z3LegacySolverFactory.getInstance())
        cfa2ConfigBuilder.encoding(CfaConfigBuilder.Encoding.LBE)
        val cfa2ExplBuilder = cfa1ConfigBuilder.ExplStrategy(phil2cfa)
        val cfa3ConfigBuilder = CfaConfigBuilder(CfaConfigBuilder.Domain.EXPL, CfaConfigBuilder.Refinement.SEQ_ITP,
            Z3LegacySolverFactory.getInstance())
        cfa3ConfigBuilder.encoding(CfaConfigBuilder.Encoding.LBE)
        val cfa3ExplBuilder = cfa1ConfigBuilder.ExplStrategy(phil3cfa)
        val cfa4ConfigBuilder = CfaConfigBuilder(CfaConfigBuilder.Domain.EXPL, CfaConfigBuilder.Refinement.SEQ_ITP,
            Z3LegacySolverFactory.getInstance())
        cfa4ConfigBuilder.encoding(CfaConfigBuilder.Encoding.LBE)
        val cfa4ExplBuilder = cfa1ConfigBuilder.ExplStrategy(phil4cfa)

        val cfaRefToPrec = RefutationToGlobalCfaPrec(ItpRefToExplPrec(), phil1cfa.initLoc)
        val dataInitPrec = ExplPrec.of(variables)
        val cfaInitPrec: CfaPrec<ExplPrec> = GlobalCfaPrec.create(dataInitPrec)

        var initExpr: Expr<BoolType> = True()
        variables.filter { it.name.contains("inited") }.forEach { initExpr = Eq(it.ref, False()) }

        val product1 = StmtMultiBuilder(cfa1ExplBuilder.multiSide, cfa1ExplBuilder.lts)
            .addRightSide(cfa2ExplBuilder.multiSide, cfa2ExplBuilder.lts)
            .build(NextSideFunctions.Nondet(), ExplInitFunc.create(solver, initExpr))
        val product2 = StmtMultiBuilder(cfa3ExplBuilder.multiSide, cfa3ExplBuilder.lts)
            .addRightSide(cfa4ExplBuilder.multiSide, cfa4ExplBuilder.lts)
            .build(NextSideFunctions.Nondet(), ExplInitFunc.create(solver, initExpr))
        val totalProduct = StmtMultiBuilder(product1.side, product1.lts)
            .addRightSide(product2.side, product2.lts)
            .build(NextSideFunctions.Nondet(), ExplInitFunc.create(solver, initExpr))

        var prop: Expr<BoolType> = True()
        variables.forEach { prop = And(prop, Eq(it.ref, True())) }
        val dataPredicate = ExplStatePredicate(prop, solver)
        val multiConfigBuilder = StmtMultiConfigBuilder.ItpStmtMultiConfigBuilder(totalProduct, prop,
            MultiStatePredicate(dataPredicate),
            RefToMultiPrec(cfaRefToPrec, cfaRefToPrec, ItpRefToExplPrec()),
            RefToMultiPrec(cfaRefToPrec, cfaRefToPrec, ItpRefToExplPrec()), ItpRefToExplPrec(),
            MultiPrec(cfaInitPrec, cfaInitPrec, dataInitPrec),
            MultiPrec(cfaInitPrec, cfaInitPrec, dataInitPrec), dataInitPrec, Z3LegacySolverFactory.getInstance(),
            logger)
        val result = multiConfigBuilder.build().check()

        Assertions.assertTrue(result.isUnsafe)
    }
}