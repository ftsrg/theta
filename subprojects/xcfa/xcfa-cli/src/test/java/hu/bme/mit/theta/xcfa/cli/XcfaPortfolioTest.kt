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

import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xcfa.cli.portfolio.ConfigNode
import hu.bme.mit.theta.xcfa.cli.portfolio.OrthogonalNode
import hu.bme.mit.theta.xcfa.cli.portfolio.STM
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.FileInputStream

class ExecCnt(var cnt: Int = 0) {
    val syncObj = Object()
    var done = false
}

val dummyChecker = { execCnt: ExecCnt, timeout: Int, endException: Throwable?, safetyResult: SafetyResult<*, *>? ->
    { _: Boolean, _: XcfaCegarConfig ->
        execCnt.cnt++
        if(timeout < 0) {
            synchronized(execCnt.syncObj) {
                if(!execCnt.done) {
                    execCnt.syncObj.wait()
                    System.err.println("Interrupted indefinite operation")
                } else {
                    System.err.println("Not starting already finished operation")
                }
            }
        } else {
            if(!execCnt.done) {
                Thread.sleep((timeout * 1000).toLong())
                System.err.println("Ended long-running operation")
            } else {
                System.err.println("Not starting already finished operation")
            }
        }
        synchronized(execCnt.syncObj) {
            execCnt.done = true
            execCnt.syncObj.notifyAll()
        }
        if (endException != null) {
            execCnt.cnt--
            System.err.println("Returning exception $endException")
            throw endException
        } else {
            execCnt.cnt--
            System.err.println("Returning result $safetyResult")
            safetyResult ?: error { "Either specify an exception, or a safety result in the test." }
        }
    }
}

class XcfaPortfolioTest {

    @Test
    fun testSimpleSyncPortfolio() {
        val cnt = ExecCnt()

        val expectedResult = SafetyResult.safe(ARG.create{ _, _ -> true})

        val config = ConfigNode(
            name = "config",
            config = XcfaCegarConfig(),
            check = dummyChecker(cnt, 0, null, expectedResult),
            inProcess = false
        )

        val stm = STM(initNode = config, edges = setOf())
        val result = try {
            stm.execute().second
        } catch (e: Throwable) {
            e
        }

        Assertions.assertEquals(0, cnt.cnt) { "Still running ${cnt.cnt} instances." }
        Assertions.assertEquals(expectedResult, result) { " $expectedResult != $result " }
    }

    @Test
    fun testSimpleAsyncPortfolio() {
        val cnt = ExecCnt()

        val expectedResult = SafetyResult.safe(ARG.create{ _, _ -> true})

        val config = ConfigNode(
            name = "config",
            config = XcfaCegarConfig(),
            check = dummyChecker(cnt, 0, null, expectedResult),
            inProcess = true
        )

        val stm = STM(initNode = config, edges = setOf())
        val result = try {
            stm.execute().second
        } catch (e: Throwable) {
            e
        }

        Assertions.assertEquals(0, cnt.cnt) { "Still running ${cnt.cnt} instances." }
        Assertions.assertEquals(expectedResult, result) { " $expectedResult != $result " }
    }

    @Test
    fun testDoubleAsyncPortfolio() {
        val cnt = ExecCnt()

        val expectedResult = SafetyResult.safe(ARG.create{ _, _ -> true})

        val config1 = ConfigNode(
            name = "config1",
            config = XcfaCegarConfig(),
            check = dummyChecker(cnt, -1, null, expectedResult),
            inProcess = true
        )

        val config2 = ConfigNode(
            name = "config2",
            config = XcfaCegarConfig(),
            check = dummyChecker(cnt, 2, null, expectedResult),
            inProcess = true
        )

        val parallelConfig = OrthogonalNode("config", STM(config1, setOf()), STM(config2, setOf()))

        val stm = STM(initNode = parallelConfig, edges = setOf())
        val result = try {
            stm.execute().second
        } catch (e: Throwable) {
            e
        }

        Assertions.assertEquals(0, cnt.cnt) { "Still running ${cnt.cnt} instances." }
        Assertions.assertEquals(expectedResult, result) { " $expectedResult != $result " }
    }

    @Test
    fun testQuadrupleAsyncPortfolio() {
        val cnt = ExecCnt()

        val expectedResult = SafetyResult.safe(ARG.create{ _, _ -> true})

        val config1 = ConfigNode(
            name = "config1",
            config = XcfaCegarConfig(),
            check = dummyChecker(cnt, -1, null, expectedResult),
            inProcess = true
        )

        val config2 = ConfigNode(
            name = "config2",
            config = XcfaCegarConfig(),
            check = dummyChecker(cnt, -1, null, expectedResult),
            inProcess = true
        )

        val config3 = ConfigNode(
            name = "config3",
            config = XcfaCegarConfig(),
            check = dummyChecker(cnt, -1, null, expectedResult),
            inProcess = true
        )

        val config4 = ConfigNode(
            name = "config4",
            config = XcfaCegarConfig(),
            check = dummyChecker(cnt, 1, null, expectedResult),
            inProcess = true
        )


        val parallelConfig = OrthogonalNode("config",
            STM(config1, setOf()),
            STM(config2, setOf()),
            STM(config3, setOf()),
            STM(config4, setOf()),
            )

        val stm = STM(initNode = parallelConfig, edges = setOf())
        val result = try {
            stm.execute().second
        } catch (e: Throwable) {
            e
        }

        Assertions.assertEquals(0, cnt.cnt) { "Still running ${cnt.cnt} instances." }
        Assertions.assertEquals(expectedResult, result) { " $expectedResult != $result " }
    }


}
