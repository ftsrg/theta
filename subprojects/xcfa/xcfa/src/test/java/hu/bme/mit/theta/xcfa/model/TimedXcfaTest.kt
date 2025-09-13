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

package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.clock.constr.ClockConstrs
import hu.bme.mit.theta.core.clock.op.ClockOps
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.clocktype.ClockType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.xcfa.model.ParamDirection.IN
import hu.bme.mit.theta.xcfa.model.ParamDirection.OUT
import org.junit.Test

class TimedXcfaTest {
    private fun getXcfa() =
        xcfa("timed-example") {
            lateinit var x: VarDecl<*>
            lateinit var c: VarDecl<*>
            global { x = "x" type Int() init "1" }
            global { c = "c" type ClockType.getInstance() init "0" }

            lateinit var y: VarDecl<*>
            lateinit var lc: VarDecl<*>
            threadlocal { y = "y" type Int() init "2" }
            threadlocal { lc = "lc" type ClockType.getInstance() init "0" }

            val proc1 =
                procedure("proc1") {
                    "a" type Int() direction IN
                    "b" type Int() direction OUT

                    (init to final) {
                        clockOp(ClockOps.Reset(lc as VarDecl<RatType>, 0))
                        clockDelay()
                        clockOp(ClockOps.Guard(ClockConstrs.Lt(lc as VarDecl<RatType>, 4)))
                        clockOp(ClockOps.Guard(ClockConstrs.Lt(c as VarDecl<RatType>, 4)))
                        "b" assign "a"
                    }
                }

            val main =
                procedure("main") {
                    val ret = "ret" type Int()

                    val thr1 = "thr1" type Int()
                    val thr2 = "thr2" type Int()
                    (init to "L0") {
                        clockOp(ClockOps.Reset(c as VarDecl<RatType>, 0))
                        proc1("1", ret.ref)
                        thr1.start(proc1, "1", ret.ref)
                        "thr2".start(proc1, "2", ret.ref)
                    }
                    ("L0" to "L1") {
                        thr1.join()
                        thr2.join()
                    }
                    ("L1" to final) { assume(Eq(x.ref as RefExpr<IntType>, y.ref as RefExpr<IntType>)) }
                    ("L1" to err) { assume("(/= x y)") }
                }

            main.start()
        }

    @Test
    fun defineXcfa() {
        val xcfa = getXcfa()
        xcfa.globalVars
    }
}