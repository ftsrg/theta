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
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class UnrollOrderTest {

  /**
   * `j` counts to 3, then `i` does. The `i` loop is countable only once the `j` loop is unrolled:
   * the search for `i`'s initialization walks back through the `j` loop's head.
   */
  private fun twoCountedLoops() =
    XcfaBuilder("")
      .procedure("main") {
        "i" type Int()
        "j" type Int()
        (init to "L1") { "i".assign("0") }
        ("L1" to "J") { "j".assign("0") }
        ("J" to "J1") {
          assume("(< j 3)")
          "j".assign("(+ j 1)")
        }
        ("J1" to "J") { skip() }
        ("J" to "I") { assume("(>= j 3)") }
        ("I" to "I1") {
          assume("(< i 3)")
          "i".assign("(+ i 1)")
        }
        ("I1" to "I") { skip() }
        ("I" to final) { assume("(>= i 3)") }
      }
      .builder

  private fun <T> withSeed(seed: Long, body: () -> T): T {
    val saved = UnrollPass.EXPLORATION_SEED
    UnrollPass.EXPLORATION_SEED = seed
    try {
      return body()
    } finally {
      UnrollPass.EXPLORATION_SEED = saved
    }
  }

  @Test
  fun countableLoopsAreNotForced() {
    for (seed in 0L until 16L) {
      val result = withSeed(seed) { UnrollPass(5).runChecked(twoCountedLoops()) }
      assertFalse(result.unsafeUnrollUsed, "seed $seed force-unrolled a loop with a known count")
    }
  }

  @Test
  fun uncountableLoopIsStillForced() {
    val builder =
      XcfaBuilder("")
        .procedure("main") {
          "i" type Int()
          "n" type Int()
          (init to "L1") { "i".assign("0") }
          ("L1" to "L2") { havoc("n") }
          ("L2" to "L3") {
            assume("(< i n)")
            "i".assign("(+ i 1)")
          }
          ("L3" to "L2") { skip() }
          ("L2" to final) { assume("(>= i n)") }
        }
        .builder
    assertTrue(UnrollPass(5).runChecked(builder).unsafeUnrollUsed)
  }
}
