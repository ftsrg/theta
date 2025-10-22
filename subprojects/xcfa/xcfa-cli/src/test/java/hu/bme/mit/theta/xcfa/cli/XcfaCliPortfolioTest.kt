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
package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.portfolio.*
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.procedure
import hu.bme.mit.theta.xcfa.model.xcfa
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class XcfaCliPortfolioTest {
  companion object {
    private object Portfolios {
      val complex23Portfolio =
        {
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: Logger ->
          complexPortfolio23(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }

      val complex24Portfolio =
        {
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: Logger ->
          complexPortfolio24(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }

      val complex25Portfolio =
        {
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: Logger ->
          complexPortfolio25(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }

      val complex26Portfolio =
        {
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: Logger ->
          complexPortfolio26(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }

      val bounded24Portfolio =
        {
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: Logger ->
          boundedPortfolio24(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }

      val bounded25Portfolio =
        {
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: Logger ->
          boundedPortfolio25(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }

      val horn25Portfolio =
        {
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: Logger ->
          hornPortfolio25(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }
    }

    private object Programs {
      val basic = XCFA("", setOf()) to ParseContext()

      val multithread =
        xcfa("") {
          val proc1 = procedure("f") { init to final }
          val main =
            procedure("main") {
              val thr1 = "thr1" type Int()
              (init to "L0") { thr1.start(proc1) }
              ("L0" to final) { thr1.join() }
            }
          main.start()
        } to ParseContext().apply { multiThreading = true }

      val float =
        XCFA("", setOf()) to ParseContext().apply { addArithmeticTrait(ArithmeticTrait.FLOAT) }

      val arr =
        XCFA("", setOf()) to ParseContext().apply { addArithmeticTrait(ArithmeticTrait.ARR) }

      val bitwise =
        XCFA("", setOf()) to ParseContext().apply { addArithmeticTrait(ArithmeticTrait.BITWISE) }

      val nonlin =
        XCFA("", setOf()) to ParseContext().apply { addArithmeticTrait(ArithmeticTrait.NONLIN_INT) }
    }

    private val defaultCheck = { stm: STM?, e: Exception? ->
      Assertions.assertNotNull(stm)
      Assertions.assertNull(e)
      val vis = stm!!.visualize()
      System.err.println(vis)
      Assertions.assertTrue(vis.isNotEmpty())
    }

    private val unsupportedCheck = { stm: STM?, e: Exception? ->
      Assertions.assertNull(stm)
      Assertions.assertNotNull(e)
      Assertions.assertTrue(e is UnsupportedOperationException)
    }

    @JvmStatic
    fun data(): Collection<Array<Any>> {
      return listOf(
        arrayOf(Portfolios.complex23Portfolio, Programs.basic, defaultCheck),
        arrayOf(Portfolios.complex23Portfolio, Programs.multithread, defaultCheck),
        arrayOf(Portfolios.complex23Portfolio, Programs.float, defaultCheck),
        arrayOf(Portfolios.complex23Portfolio, Programs.arr, defaultCheck),
        arrayOf(Portfolios.complex23Portfolio, Programs.bitwise, defaultCheck),
        arrayOf(Portfolios.complex23Portfolio, Programs.nonlin, defaultCheck),
        arrayOf(Portfolios.complex24Portfolio, Programs.basic, defaultCheck),
        arrayOf(Portfolios.complex24Portfolio, Programs.multithread, defaultCheck),
        arrayOf(Portfolios.complex24Portfolio, Programs.float, defaultCheck),
        arrayOf(Portfolios.complex24Portfolio, Programs.arr, defaultCheck),
        arrayOf(Portfolios.complex24Portfolio, Programs.bitwise, defaultCheck),
        arrayOf(Portfolios.complex24Portfolio, Programs.nonlin, defaultCheck),
        arrayOf(Portfolios.complex25Portfolio, Programs.basic, defaultCheck),
        arrayOf(Portfolios.complex25Portfolio, Programs.multithread, defaultCheck),
        arrayOf(Portfolios.complex25Portfolio, Programs.float, defaultCheck),
        arrayOf(Portfolios.complex25Portfolio, Programs.arr, defaultCheck),
        arrayOf(Portfolios.complex25Portfolio, Programs.bitwise, defaultCheck),
        arrayOf(Portfolios.complex25Portfolio, Programs.nonlin, defaultCheck),
        arrayOf(Portfolios.complex26Portfolio, Programs.basic, defaultCheck),
        arrayOf(Portfolios.complex26Portfolio, Programs.multithread, defaultCheck),
        arrayOf(Portfolios.complex26Portfolio, Programs.float, defaultCheck),
        arrayOf(Portfolios.complex26Portfolio, Programs.arr, defaultCheck),
        arrayOf(Portfolios.complex26Portfolio, Programs.bitwise, defaultCheck),
        arrayOf(Portfolios.complex26Portfolio, Programs.nonlin, defaultCheck),
        arrayOf(Portfolios.bounded24Portfolio, Programs.basic, defaultCheck),
        arrayOf(Portfolios.bounded24Portfolio, Programs.multithread, unsupportedCheck),
        arrayOf(Portfolios.bounded24Portfolio, Programs.float, defaultCheck),
        arrayOf(Portfolios.bounded24Portfolio, Programs.arr, defaultCheck),
        arrayOf(Portfolios.bounded24Portfolio, Programs.bitwise, defaultCheck),
        arrayOf(Portfolios.bounded24Portfolio, Programs.nonlin, defaultCheck),
        arrayOf(Portfolios.bounded25Portfolio, Programs.basic, defaultCheck),
        arrayOf(Portfolios.bounded25Portfolio, Programs.multithread, unsupportedCheck),
        arrayOf(Portfolios.bounded25Portfolio, Programs.float, defaultCheck),
        arrayOf(Portfolios.bounded25Portfolio, Programs.arr, defaultCheck),
        arrayOf(Portfolios.bounded25Portfolio, Programs.bitwise, defaultCheck),
        arrayOf(Portfolios.bounded25Portfolio, Programs.nonlin, defaultCheck),
        arrayOf(Portfolios.horn25Portfolio, Programs.basic, defaultCheck),
        arrayOf(Portfolios.horn25Portfolio, Programs.multithread, unsupportedCheck),
        arrayOf(Portfolios.horn25Portfolio, Programs.float, defaultCheck),
        arrayOf(Portfolios.horn25Portfolio, Programs.arr, defaultCheck),
        arrayOf(Portfolios.horn25Portfolio, Programs.bitwise, defaultCheck),
        arrayOf(Portfolios.horn25Portfolio, Programs.nonlin, defaultCheck),
      )
    }
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testPortfolio(
    portfolio:
      (
        xcfa: XCFA,
        mcm: MCM,
        parseContext: ParseContext,
        portfolioConfig: XcfaConfig<*, *>,
        logger: Logger,
        uniqueLogger: Logger,
      ) -> STM,
    program: Pair<XCFA, ParseContext>,
    check: (STM?, Exception?) -> Unit,
  ) {
    val (stm, exception) =
      try {
        portfolio(
          program.first,
          emptySet(),
          program.second,
          XcfaConfig<SpecFrontendConfig, SpecBackendConfig>(),
          NullLogger.getInstance(),
          NullLogger.getInstance(),
        ) to null
      } catch (e: Exception) {
        System.err.println(e.stackTraceToString())
        null to e
      }
    check(stm, exception)
  }
}
