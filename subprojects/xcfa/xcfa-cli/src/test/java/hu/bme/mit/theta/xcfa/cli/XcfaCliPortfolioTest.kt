/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.portfolio.STM
import hu.bme.mit.theta.xcfa.cli.portfolio.complexPortfolio23
import hu.bme.mit.theta.xcfa.cli.portfolio.complexPortfolio24
import hu.bme.mit.theta.xcfa.model.XCFA
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.util.stream.Stream

class XcfaCliPortfolioTest {
    companion object {


        @JvmStatic
        fun portfolios(): Stream<Arguments> {
            return Stream.of(
                Arguments.of({ xcfaTyped: XCFA,
                    cFileNameTyped: String,
                    loggerTyped: Logger,
                    smtHomeTyped: String,
                    traitsTyped: VerificationTraits,
                    propertyTyped: ErrorDetection,
                    parseContextTyped: ParseContext,
                    argdebug: Boolean ->
                    complexPortfolio23(xcfaTyped, cFileNameTyped, loggerTyped, smtHomeTyped, traitsTyped, propertyTyped,
                        parseContextTyped, argdebug)
                }),
                Arguments.of({ xcfaTyped: XCFA,
                    cFileNameTyped: String,
                    loggerTyped: Logger,
                    smtHomeTyped: String,
                    traitsTyped: VerificationTraits,
                    propertyTyped: ErrorDetection,
                    parseContextTyped: ParseContext,
                    argdebug: Boolean ->
                    complexPortfolio24(xcfaTyped, cFileNameTyped, loggerTyped, smtHomeTyped, traitsTyped, propertyTyped,
                        parseContextTyped, argdebug)
                }),
            )
        }

    }

    @ParameterizedTest
    @MethodSource("portfolios")
    fun testPortfolio(portfolio: (xcfaTyped: XCFA,
        cFileNameTyped: String,
        loggerTyped: Logger,
        smtHomeTyped: String,
        traitsTyped: VerificationTraits,
        propertyTyped: ErrorDetection,
        parseContextTyped: ParseContext,
        argdebug: Boolean) -> STM) {

        val stm = portfolio(XCFA("name", setOf()), "", NullLogger.getInstance(), "", VerificationTraits(),
            ErrorDetection.ERROR_LOCATION, ParseContext(), false)

        Assertions.assertTrue(stm.visualize().isNotEmpty())

    }


}
