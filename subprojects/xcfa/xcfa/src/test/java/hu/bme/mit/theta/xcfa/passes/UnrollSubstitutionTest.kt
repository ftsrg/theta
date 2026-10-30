/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class UnrollSubstitutionTest {

  @Test
  fun uncountableLoopIsForcedWhenSubstitutingTheLoopVariable() {
    // `i` is the loop variable, but its update shares an edge with `c`, so the loop is not counted.
    val builder =
      XcfaBuilder("")
        .procedure("main") {
          "i" type Int()
          "c" type Int()
          (init to "L1") { "i".assign("0") }
          ("L1" to "L2") { assume("(< i 10)") }
          ("L2" to "L1") {
            havoc("c")
            "i".assign("(+ i 1)")
          }
          ("L1" to final) { assume("(>= i 10)") }
        }
        .builder
    val pass = UnrollPass(2, substituteLoopVar = true, parseContext = ParseContext())
    assertTrue(pass.runChecked(builder).unsafeUnrollUsed)
  }
}
