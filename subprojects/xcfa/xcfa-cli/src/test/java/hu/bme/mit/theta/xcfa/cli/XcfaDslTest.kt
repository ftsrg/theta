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

import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.z3.Z3SolverManager
import hu.bme.mit.theta.xcfa.model.ParamDirection.IN
import hu.bme.mit.theta.xcfa.model.ParamDirection.OUT
import hu.bme.mit.theta.xcfa.model.procedure
import hu.bme.mit.theta.xcfa.model.xcfa
import org.junit.Assert
import org.junit.Test

class XcfaDslTest {

    private fun getSyncXcfa() = xcfa("example") {
        val proc1 = procedure("proc1") {
            val a = "a" type Int() direction IN
            val b = "b" type Int() direction OUT

            (init to final) {
                b assign a.ref
            }
        }
        val main = procedure("main") {
            val tmp = "tmp" type Int()
            (init to "L1") {
                proc1("1", tmp.ref)
            }
            ("L1" to final) {
                assume("(= tmp 1)")
            }
            ("L1" to err) {
                assume("(/= tmp 1)")
            }
        }

        main.start()
    }

    private fun getAsyncXcfa() = xcfa("example") {
        val proc1 = procedure("proc1") {
            val a = "a" type Int() direction IN
            val b = "b" type Int() direction OUT

            (init to final) {
                b assign a.ref
            }
        }
        val main = procedure("main") {
            val tmp = "tmp" type Int()
            val thr1 = "thr1" type Int()
            (init to "L1") {
                thr1.start(proc1, "1", tmp.ref)
            }
            ("L1" to final) {
                thr1.join()
                assume("(= tmp 1)")
            }
            ("L1" to err) {
                thr1.join()
                assume("(/= tmp 1)")
            }
        }

        main.start()
    }

    @Test
    fun verifyXcfa() {
        SolverManager.registerSolverManager(Z3SolverManager.create())
        val config = XcfaCegarConfig(maxEnum = 1, search = Search.BFS, initPrec = InitPrec.ALLVARS)
        run {
            val xcfa = getSyncXcfa()
            val safetyResult = config.check(xcfa, ConsoleLogger(Logger.Level.DETAIL))
            Assert.assertTrue(safetyResult.isSafe)
        }
        run {
            val xcfa = getAsyncXcfa()
            val safetyResult = config.check(xcfa, ConsoleLogger(Logger.Level.DETAIL))
            Assert.assertTrue(safetyResult.isUnsafe)
        }
    }

}