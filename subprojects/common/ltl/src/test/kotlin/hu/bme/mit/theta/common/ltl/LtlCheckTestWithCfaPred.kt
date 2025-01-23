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
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.multi.NextSideFunctions
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder
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
class LtlCheckTestWithCfaPred(
  private val cfaName: String,
  private val ltlExpr: String,
  private val result: Boolean,
  private val searchStrategy: LoopcheckerSearchStrategy,
  private val refinerStrategy: ASGTraceCheckerStrategy,
) {

  private val itpSolverFactory = Z3LegacySolverFactory.getInstance()
  private val abstractionSolver: Solver = Z3LegacySolverFactory.getInstance().createSolver()
  private val logger: Logger = ConsoleLogger(Logger.Level.INFO)

  companion object {
    fun data() =
      listOf(
        arrayOf("wave_flags", "F G(x)", false),
        arrayOf("wave_flags", "F G(x and y)", false),
        arrayOf("wave_flag", "G F(x)", true),
        arrayOf("wave_flag", "G(x)", false),
        arrayOf("wave_flag", "F G(x)", false),
        arrayOf("counter5inf", "G(not(x=6))", true),
        arrayOf("counter5inf", "G(x=1)", false),
        arrayOf("counter5inf", "G(x=5)", false),
        arrayOf("counter5inf", "F G(x=5)", true),
        arrayOf("counter5inf", "F(x=1)", true),
        arrayOf("counter5inf", "F(x=5)", true),
        arrayOf("wave_flags", "G F(y)", true),
        arrayOf("wave_flags", "F G(x)", false),
        arrayOf("indicator", "G (x -> y)", true),
        //                arrayOf("indicator_multiassign", "G (x -> y)", true),
        arrayOf("indicator", "G (x -> X (not x))", true),
        arrayOf("indicator", "G (y -> X (not y))", false),
      )

    @JvmStatic
    @Parameterized.Parameters(name = "{3}-{4}: {0}")
    fun params() =
      listOf(LoopcheckerSearchStrategy.GDFS, LoopcheckerSearchStrategy.NDFS).flatMap { search ->
        listOf(ASGTraceCheckerStrategy.DIRECT_REFINEMENT, ASGTraceCheckerStrategy.BOUNDED_UNROLLING).flatMap {
          ref ->
          data().map { arrayOf(*it, search, ref) }
        }
      }
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
          CfaConfigBuilder.Domain.PRED_SPLIT,
          CfaConfigBuilder.Refinement.SEQ_ITP,
          itpSolverFactory,
        )
        .encoding(CfaConfigBuilder.Encoding.SBE)
        .PredStrategy(cfa)
    val variables = cfa.vars
    val dataAnalysis =
      PredAnalysis.create<ExprAction>(
        abstractionSolver,
        PredAbstractors.booleanSplitAbstractor(abstractionSolver),
        True(),
      )
    val refToPrec = RefutationToGlobalCfaPrec(ItpRefToPredPrec(ExprSplitters.atoms()), cfa.initLoc)
    val dataInitPrec = PredPrec.of()

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
        searchStrategy,
        refinerStrategy,
        Ltl2BuchiThroughHoaf(Ltl2HoafFromDir("src/test/resources/hoa"), logger),
        variables,
        nextSideFunction = NextSideFunctions.Alternating(),
      )

    Assert.assertEquals(result, checker.check(configBuilder.createInitPrec(), dataInitPrec).isSafe)
  }
}
