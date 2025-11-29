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
package hu.bme.mit.theta.sts.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.PredicateAbstractionMEPass
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.refinement.createFwBinItpCheckerFactory
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.sts.STS
import hu.bme.mit.theta.sts.aiger.AigerParser
import hu.bme.mit.theta.sts.aiger.AigerToSts
import hu.bme.mit.theta.sts.analysis.pipeline.StsPipelineChecker
import hu.bme.mit.theta.sts.dsl.StsDslManager
import java.io.FileInputStream
import java.io.IOException
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class StsAbstractMonolithicTest() {

  companion object {
    @JvmStatic
    fun data(): Collection<Arguments> {
      return listOf(

        //                    {"src/test/resources/hw1_false.aag", false},
        //                    {"src/test/resources/hw2_true.aag", true},
        //                    {"src/test/resources/boolean1.system", false},
        //                    {"src/test/resources/boolean2.system", false},
        Arguments.of("src/test/resources/counter.system", true),
        Arguments.of("src/test/resources/counter_bad.system", false),
        Arguments.of("src/test/resources/counter_parametric.system", true),

        //                {"src/test/resources/loop.system", true},
        Arguments.of("src/test/resources/loop_bad.system", false),
        Arguments.of("src/test/resources/multipleinitial.system", false),
        Arguments.of("src/test/resources/readerswriters.system", true),
        Arguments.of("src/test/resources/simple1.system", false),
        Arguments.of("src/test/resources/simple2.system", true),
        Arguments.of("src/test/resources/simple3.system", false),
      )
    }
  }

  @Throws(IOException::class)
  private fun runTest(
    filePath: String,
    expectedResult: Boolean,
    logger: Logger,
    checkerBuilderFunction:
      (MonolithicExpr) -> SafetyChecker<out InvariantProof, Trace<ExplState, ExprAction>, UnitPrec>,
  ) {
    val sts: STS
    if (filePath.endsWith("aag")) {
      sts = AigerToSts.createSts(AigerParser.parse(filePath))
    } else {
      val spec = StsDslManager.createStsSpec(FileInputStream(filePath))
      if (spec.allSts.size != 1) {
        throw UnsupportedOperationException("STS contains multiple properties.")
      }
      sts = Utils.singleElementOf(spec.allSts)
    }

    val passes =
      mutableListOf<MonolithicExprPass<InvariantProof>>(
        PredicateAbstractionMEPass(
          createFwBinItpCheckerFactory(Z3LegacySolverFactory.getInstance())
        )
      )

    val checker = StsPipelineChecker(sts, checkerBuilderFunction, passes, logger = logger)

    Assertions.assertEquals(expectedResult, checker.check().isSafe())
  }

  //    @Test
  //    public void testIc3() throws IOException {
  //        final Logger logger = new ConsoleLogger(Logger.Level.VERBOSE);
  //        final var solverFactory = Z3LegacySolverFactory.getInstance();
  //
  //        runTest(
  //            logger,
  //            solverFactory,
  //            abstractMe -> new Ic3Checker<>(
  //                    abstractMe,
  //                    true,
  //                    solverFactory,
  //                    valuation -> abstractMe.getValToState().invoke(valuation),
  //                    (Valuation v1, Valuation v2) -> abstractMe.getBiValToAction().invoke(v1,
  // v2),
  //                    true,
  //                    true,
  //                    true,
  //                    true,
  //                    true,
  //                    true,
  //                    logger)
  //        );
  //    }
  //
  //    @Test
  //    public void testBMC() throws IOException {
  //        final Logger logger = new ConsoleLogger(Logger.Level.VERBOSE);
  //        final var solverFactory = Z3LegacySolverFactory.getInstance();
  //
  //        runTest(
  //                logger,
  //                solverFactory,
  //                abstractMe -> BoundedCheckerBuilderKt.buildBMC(
  //                        abstractMe,
  //                        solverFactory.createSolver(),
  //                        val -> abstractMe.getValToState().invoke(val),
  //                        (val1, val2) ->
  //                                abstractMe.getBiValToAction().invoke(val1, val2),
  //                        logger)
  //        );
  //    }
  @ParameterizedTest
  @MethodSource("data")
  @Throws(IOException::class)
  fun testMdd(filePath: String, expectedResult: Boolean) {
    val logger: Logger = ConsoleLogger(Logger.Level.VERBOSE)
    val solverFactory = Z3LegacySolverFactory.getInstance()

    try {
      SolverPool(solverFactory).use { solverPool ->
        runTest(
          filePath,
          expectedResult,
          logger,
          { monolithicExpr: MonolithicExpr? -> MddChecker(monolithicExpr!!, solverPool, logger) },
        )
      }
    } catch (e: Exception) {
      throw RuntimeException(e)
    }
  }
}
