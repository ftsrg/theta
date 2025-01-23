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
package hu.bme.mit.theta.common.ltl

import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopCheckerSearchStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.multi.NextSideFunctions
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.common.cfa.buchi.hoa.Ltl2BuchiThroughHoaf
import hu.bme.mit.theta.common.cfa.buchi.hoa.Ltl2HoafFromDir
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import hu.bme.mit.theta.xsts.passes.XstsNormalizerPass
import java.io.FileInputStream
import junit.framework.TestCase.fail
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

@RunWith(Parameterized::class)
class LtlCheckTestWithXstsExpl(
  private val xstsName: String,
  private val ltlExpr: String,
  private val result: Boolean,
) {

  private val solverFactory = Z3LegacySolverFactory.getInstance()
  private val logger: Logger = ConsoleLogger(Logger.Level.VERBOSE)

  companion object {
    @JvmStatic
    @Parameterized.Parameters
    fun data() =
      listOf(
        arrayOf("counter3inf", "F G(x=3)", true),
        arrayOf("counter3inf", "F(x=2)", true),
        arrayOf("counter3inf", "G(x<4)", true),
        arrayOf("counter3inf", "G(x=1)", false),
        arrayOf("counter6to7", "G(x=1)", false),
        arrayOf("counter6to7", "G(x=7)", false),
        arrayOf("counter6to7", "G F(x=7)", true),
      )
  }

  @Test
  fun test() {
    var xstsI: XSTS?
    FileInputStream(String.format("src/test/resources/xsts/%s.xsts", xstsName)).use { inputStream ->
      xstsI = XstsDslManager.createXsts(inputStream)
    }
    if (xstsI == null) fail("Couldn't read xsts $xstsName")
    val xsts = XstsNormalizerPass.transform(xstsI!!)
    val configBuilder: XstsConfigBuilder.ExplStrategy =
      XstsConfigBuilder(
          XstsConfigBuilder.Domain.EXPL,
          XstsConfigBuilder.Refinement.SEQ_ITP,
          solverFactory,
          solverFactory,
        )
        .initPrec(XstsConfigBuilder.InitPrec.EMPTY)
        .ExplStrategy(xsts)
    val initPrec = configBuilder.initPrec

    val checker:
      LtlChecker<
        XstsState<ExplState>,
        XstsState<UnitState>,
        XstsAction,
        ExplPrec,
        UnitPrec,
        ExplPrec,
        ExplState,
      > =
      LtlChecker(
        configBuilder.multiSide,
        configBuilder.lts,
        configBuilder.itpRefToPrec,
        configBuilder.itpRefToPrec,
        configBuilder.dataAnalysis,
        ltlExpr,
        solverFactory,
        logger,
        LoopCheckerSearchStrategy.GDFS,
        ASGTraceCheckerStrategy.DIRECT_REFINEMENT,
        Ltl2BuchiThroughHoaf(Ltl2HoafFromDir("src/test/resources/hoa"), logger),
        xsts.vars,
        xsts.initFormula,
        NextSideFunctions.Alternating(),
      )
    val checkResult = checker.check(initPrec, initPrec)

    Assert.assertEquals(result, checkResult.isSafe)
  }
}
