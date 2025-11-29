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
import hu.bme.mit.theta.analysis.pred.ExprSplitters
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec
import hu.bme.mit.theta.common.cfa.buchi.hoa.Ltl2BuchiThroughHoaf
import hu.bme.mit.theta.common.cfa.buchi.hoa.Ltl2HoafFromDir
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import hu.bme.mit.theta.xsts.passes.XstsNormalizerPass
import java.io.FileInputStream
import junit.framework.TestCase.fail
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class LtlCheckTestWithXstsPred(
  private val xstsName: String,
  private val ltlExpr: String,
  private val result: Boolean,
  private val searchStrategy: LoopCheckerSearchStrategy,
  private val refinerStrategy: ASGTraceCheckerStrategy,
) {

  private val itpSolverFactory = Z3LegacySolverFactory.getInstance()
  private val abstractionSolver: Solver = Z3LegacySolverFactory.getInstance().createSolver()
  private val logger: Logger = ConsoleLogger(Logger.Level.INFO)

  companion object {
    private fun data() =
      listOf(
        arrayOf("simple_types", "F G(color = Colors.Red)", false),
        arrayOf("counter3inf", "F G(x=3)", true),
        arrayOf("counter3inf", "F(x=2)", true),
        arrayOf("counter3inf", "G(x<4)", true),
        arrayOf("counter3inf", "G(x=1)", false),
        arrayOf("counter6to7", "G(x=1)", false),
        arrayOf("counter6to7", "G(x=7)", false),
        arrayOf("counter6to7", "G F(x=7)", true),
        //        arrayOf("counter50", "G(x<49)", false),
        arrayOf(
          "trafficlight_v2",
          "G(LightCommands_displayRed -> X(not LightCommands_displayGreen))",
          true,
        ),
        arrayOf(
          "trafficlight_v2",
          "G((main_region = Main_region.Normal and normal = Normal.Red and (not PoliceInterrupt_police) and Control_toggle  and (X(not PoliceInterrupt_police))) -> X(X(normal = Normal.Green)))",
          true,
        ),
        arrayOf(
          "trafficlight_v2",
          "G(PoliceInterrupt_police -> F(LightCommands_displayYellow))",
          true,
        ),
        arrayOf("forever5", "G(x=5)", true),
        arrayOf("forever5", "F(x=6)", false),
        arrayOf("randomincreasingeven", "not F(x=1)", true),
        arrayOf("randomincreasingeven", "F(x>10)", true),
        arrayOf("randomincreasingeven", "G(x>=0)", true),
        arrayOf("simple_color", "G(envColor = Colors.Green -> X(modelColor = Colors.Blue))", true),
        arrayOf(
          "simple_color",
          "G(envColor = Colors.Green -> X(modelColor = Colors.Green))",
          false,
        ),
        arrayOf("simple_color", "F G(envColor = modelColor)", false),
        arrayOf("weather", "G F(isClever and isWet)", false),
        arrayOf("weather", "F G(not isWet)", true),
        arrayOf(
          "weather",
          "G(time = TimeOfDay.Noon -> X(time = TimeOfDay.Noon or time = TimeOfDay.Afternoon))",
          true,
        ),
        //            arrayOf("weather", "F G(weather = Weather.Foggy -> (clothing =
        // Clothing.Nothing or clothing = Clothing.Warm))", true),
        //            arrayOf("weather_noinit", "G F(isClever and isWet)", false),
        //            arrayOf("weather_noinit", "F G(not isWet)", true),
        //            arrayOf("weather_noinit", "G(time = TimeOfDay.Noon -> X(time = TimeOfDay.Noon
        // or time = TimeOfDay.Afternoon))", true),
        //            arrayOf("weather_noinit", "F G(weather = Weather.Foggy -> (clothing =
        // Clothing.Nothing or clothing = Clothing.Warm))", true),
      )

    @JvmStatic
    fun params() =
      listOf(LoopCheckerSearchStrategy.GDFS, LoopCheckerSearchStrategy.NDFS).flatMap { search ->
        ASGTraceCheckerStrategy.entries.flatMap { ref -> data().map { arrayOf(*it, search, ref) } }
      }
  }

  @ParameterizedTest
  @MethodSource("params")
  fun test(
    xstsName: String,
    ltlExpr: String,
    result: Boolean,
    searchStrategy: LoopCheckerSearchStrategy,
    refinerStrategy: ASGTraceCheckerStrategy,
  ) {
    var xstsI: XSTS?
    FileInputStream("src/test/resources/xsts/$xstsName.xsts").use { inputStream ->
      xstsI = XstsDslManager.createXsts(inputStream)
    }
    if (xstsI == null) fail("Couldn't read xsts $xstsName")
    val xsts = XstsNormalizerPass.transform(xstsI!!)
    val configBuilder =
      XstsConfigBuilder(
          XstsConfigBuilder.Domain.PRED_SPLIT,
          XstsConfigBuilder.Refinement.SEQ_ITP,
          itpSolverFactory,
          itpSolverFactory,
        )
        .initPrec(XstsConfigBuilder.InitPrec.EMPTY)
        .PredStrategy(xsts)
    val variables = xsts.vars
    val refToPrec = ItpRefToPredPrec(ExprSplitters.atoms())
    val initPrec = configBuilder.initPrec

    val checker =
      LtlChecker(
        configBuilder.multiSide,
        configBuilder.lts,
        refToPrec,
        refToPrec,
        configBuilder.dataAnalysis,
        ltlExpr,
        itpSolverFactory,
        logger,
        searchStrategy,
        refinerStrategy,
        Ltl2BuchiThroughHoaf(Ltl2HoafFromDir("src/test/resources/hoa"), logger),
        variables,
        xsts.initFormula,
      )

    val safetyResult = checker.check(initPrec, initPrec)
    Assertions.assertEquals(result, safetyResult.isSafe)
  }
}
