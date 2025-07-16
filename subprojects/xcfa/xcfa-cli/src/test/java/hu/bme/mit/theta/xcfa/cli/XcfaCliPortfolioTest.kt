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

import hu.bme.mit.theta.common.logging.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.portfolio.*
import hu.bme.mit.theta.xcfa.model.XCFA
import java.util.stream.Stream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class XcfaCliPortfolioTest {
  companion object {

    @JvmStatic
    fun portfolios(): Stream<Arguments> {
      return Stream.of(
        Arguments.of({
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: UniqueWarningLogger ->
          complexPortfolio23(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }),
        Arguments.of({
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: UniqueWarningLogger ->
          complexPortfolio24(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }),
        Arguments.of({
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: UniqueWarningLogger ->
          complexPortfolio25(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }),
        Arguments.of({
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: UniqueWarningLogger ->
          boundedPortfolio24(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }),
        Arguments.of({
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: UniqueWarningLogger ->
          boundedPortfolio25(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }),
        Arguments.of({
          xcfa: XCFA,
          mcm: MCM,
          parseContext: ParseContext,
          portfolioConfig: XcfaConfig<*, *>,
          logger: Logger,
          uniqueLogger: UniqueWarningLogger ->
          hornPortfolio25(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
        }),
      )
    }
  }

  @ParameterizedTest
  @MethodSource("portfolios")
  fun testPortfolio(
    portfolio:
      (
        xcfa: XCFA,
        mcm: MCM,
        parseContext: ParseContext,
        portfolioConfig: XcfaConfig<*, *>,
        logger: Logger,
        uniqueLogger: UniqueWarningLogger,
      ) -> STM
  ) {
    val stm =
      portfolio(
        XCFA("name", setOf()),
        emptySet(),
        ParseContext(),
        XcfaConfig<SpecFrontendConfig, SpecBackendConfig>(),
        NullLogger.getInstance(),
        UniqueWarningLogger(NullLogger.getInstance())
      )

    val vis = stm.visualize()
    System.err.println(vis)
    Assertions.assertTrue(vis.isNotEmpty())
  }
}
