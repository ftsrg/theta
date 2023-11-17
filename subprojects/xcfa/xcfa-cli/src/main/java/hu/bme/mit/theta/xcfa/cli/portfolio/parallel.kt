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

package hu.bme.mit.theta.xcfa.cli.portfolio

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.BaseLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.Domain
import hu.bme.mit.theta.xcfa.cli.Refinement
import hu.bme.mit.theta.xcfa.cli.VerificationTraits
import hu.bme.mit.theta.xcfa.cli.XcfaCegarConfig
import hu.bme.mit.theta.xcfa.model.XCFA

fun parallel(xcfa: XCFA, cFileName: String, loggerTyped: Logger, smtHome: String,
    traitsTyped: VerificationTraits, propertyTyped: ErrorDetection, parseContext: ParseContext, argdebug: Boolean)
    : Pair<XcfaCegarConfig, SafetyResult<*, *>>{

    val checker = { logger: Logger -> { p: Boolean, config: XcfaCegarConfig ->
        if (p)
            config.checkInProcess(xcfa, smtHome, true, cFileName, logger, parseContext, argdebug)()
        else config.check(xcfa, loggerTyped)
    } }


    val config1 = ConfigNode(
        name = "config1",
        config = XcfaCegarConfig(domain = Domain.EXPL, maxEnum = 1000, refinement = Refinement.NWT_IT_WP),
        check = checker(object: BaseLogger(Logger.Level.INFO) {
            override fun writeStr(str: String?) {
                System.err.print(str)
            }
        }),
        inProcess = true
    )

    val config2 = ConfigNode(
        name = "config2",
        config = XcfaCegarConfig(maxEnum = 1),
        check = checker(object: BaseLogger(Logger.Level.INFO) {
            override fun writeStr(str: String?) {
                System.out.print(str)
            }
        }),
        inProcess = true
    )

    val parallelConfig = OrthogonalNode("config", STM(config1, setOf()), STM(config2, setOf()))

    val stm = STM(initNode = parallelConfig, edges = setOf())

    return stm.execute() as Pair<XcfaCegarConfig, SafetyResult<*, *>>
}
