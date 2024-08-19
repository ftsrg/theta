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
import hu.bme.mit.theta.analysis.multi.MultiStatePredicate
import hu.bme.mit.theta.analysis.multi.NextSideFunctions
import hu.bme.mit.theta.analysis.multi.builder.stmt.StmtMultiBuilder
import hu.bme.mit.theta.analysis.multi.config.StmtMultiConfigBuilder
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import org.junit.Test
import org.junit.jupiter.api.Assertions.assertTrue
import java.io.FileInputStream
import java.io.IOException
import java.io.SequenceInputStream

class MultiSelfProductTest {

    val logger: Logger = ConsoleLogger(Logger.Level.SUBSTEP)
    val solver: Solver = Z3LegacySolverFactory.getInstance().createSolver()

    @Test
    fun test() {
        var xsts: XSTS
        try {
            SequenceInputStream(
                FileInputStream("src/test/resources/xsts/incr_double.xsts"),
                FileInputStream("src/test/resources/xsts/xneq12.prop")
            ).use { inputStream ->
                xsts = XstsDslManager.createXsts(inputStream)
            }
        } catch (e: IOException) {
            throw RuntimeException(e)
        }
        val variables = xsts.vars

        val xstsConfigBuilder = XstsConfigBuilder(
            XstsConfigBuilder.Domain.EXPL,
            XstsConfigBuilder.Refinement.SEQ_ITP,
            Z3LegacySolverFactory.getInstance(),
            Z3LegacySolverFactory.getInstance()
        )
        val xstsExplBuilder1 = xstsConfigBuilder.ExplStrategy(xsts)
        val xstsExplBuilder2 = xstsConfigBuilder.ExplStrategy(xsts)

        val dataAnalysis = xstsExplBuilder1.dataAnalysis
        val dataInitPrec = ExplPrec.of(variables)

        val product = StmtMultiBuilder(xstsExplBuilder1.multiSide, xstsExplBuilder1.lts)
            .addRightSide(xstsExplBuilder2.multiSide, xstsExplBuilder2.lts)
            .build(NextSideFunctions.Alternating(), dataAnalysis.initFunc)
        val prop = Not(xsts.prop)
        val dataPredicate = ExplStatePredicate(prop, solver)
        val multiConfigBuilder = StmtMultiConfigBuilder.ItpStmtMultiConfigBuilder(
            product, prop,
            MultiStatePredicate(dataPredicate),
            ItpRefToExplPrec(), ItpRefToExplPrec(), ItpRefToExplPrec(), dataInitPrec,
            dataInitPrec, dataInitPrec, Z3LegacySolverFactory.getInstance(), logger
        )
        val result = multiConfigBuilder.build().check()

        assertTrue(result.isUnsafe)

    }
}