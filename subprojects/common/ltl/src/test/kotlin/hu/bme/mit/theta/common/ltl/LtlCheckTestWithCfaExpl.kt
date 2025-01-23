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
package hu.bme.mit.theta.common.ltl

import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopcheckerSearchStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy
import hu.bme.mit.theta.analysis.expl.ExplAnalysis
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.multi.NextSideFunctions
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.CfaPrec
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec
import hu.bme.mit.theta.cfa.analysis.prec.RefutationToGlobalCfaPrec
import hu.bme.mit.theta.cfa.dsl.CfaDslManager
import hu.bme.mit.theta.common.cfa.buchi.hoa.Ltl2BuchiThroughHoaf
import hu.bme.mit.theta.common.cfa.buchi.hoa.Ltl2HoafFromDir
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import java.io.FileInputStream
import junit.framework.TestCase.fail
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

@RunWith(Parameterized::class)
class LtlCheckTestWithCfaExpl(
  private val cfaName: String,
  private val ltlExpr: String,
  private val result: Boolean,
) {

  private val itpSolverFactory = Z3LegacySolverFactory.getInstance()
  private val abstractionSolver: Solver = Z3LegacySolverFactory.getInstance().createSolver()
  private val logger: Logger = ConsoleLogger(Logger.Level.VERBOSE)

  companion object {
    @JvmStatic
    @Parameterized.Parameters
    fun data() =
      listOf(
        arrayOf("counter2inf", "G(x=1)", false),
        arrayOf("counter2inf", "G(x=2)", false),
        arrayOf("counter2inf", "F G(x=2)", true),
        arrayOf("counter2inf", "F(x=1)", true),
        arrayOf("counter2inf", "F(x=3)", false),
      )
  }

  @Test
  fun test() {
    abstractionSolver.reset()
    var cfaI: CFA?
    FileInputStream(String.format("src/test/resources/cfa/%s.cfa", cfaName)).use { inputStream ->
      cfaI = CfaDslManager.createCfa(inputStream)
    }
    if (cfaI == null) fail("Couldn't read cfa $cfaName")
    val cfa = cfaI!!
    val configBuilder =
      CfaConfigBuilder(
          CfaConfigBuilder.Domain.EXPL,
          CfaConfigBuilder.Refinement.SEQ_ITP,
          itpSolverFactory,
        )
        .encoding(CfaConfigBuilder.Encoding.SBE)
        .ExplStrategy(cfa)
    val dataAnalysis = ExplAnalysis.create(abstractionSolver, True())
    val refToPrec = RefutationToGlobalCfaPrec(ItpRefToExplPrec(), cfa.initLoc)
    val variables = cfa.vars
    val dataInitPrec = ExplPrec.of(variables)
    val initPrec: CfaPrec<ExplPrec> = GlobalCfaPrec.create(dataInitPrec)

    val checker =
      LtlChecker(
        configBuilder.multiSide,
        configBuilder.lts,
        refToPrec,
        configBuilder.itpRefToPrec,
        dataAnalysis,
        ltlExpr,
        itpSolverFactory,
        logger,
        LoopcheckerSearchStrategy.GDFS,
        ASGTraceCheckerStrategy.DIRECT_REFINEMENT,
        Ltl2BuchiThroughHoaf(Ltl2HoafFromDir("src/test/resources/hoa"), logger),
        variables,
        nextSideFunction = NextSideFunctions.Alternating(),
      )

    Assert.assertEquals(result, checker.check(initPrec, dataInitPrec).isSafe)
  }
}
