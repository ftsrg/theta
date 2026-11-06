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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.passes.LbePass
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

/**
 * Every C loop keeps a location marked as the head where its guard is evaluated, through all
 * passes, and knows the variables in scope there. The loops are the lines marked `// loop`, the
 * variables in scope at each guard follow the marker.
 */
class LoopHeadTest {

  private val source = javaClass.getResource("/loop-heads.c")!!.readText()

  @ParameterizedTest
  @EnumSource(value = LbePass.LbeLevel::class, names = ["NO_LBE", "LBE_SEQ"])
  fun testEveryLoopKeepsItsHead(lbeLevel: LbePass.LbeLevel) {
    val defaultLevel = LbePass.defaultLevel
    LbePass.defaultLevel = lbeLevel
    val xcfa =
      try {
        getXcfaFromC(
            source.byteInputStream(),
            ParseContext(),
            false,
            XcfaProperty(ErrorDetection.ERROR_LOCATION),
            NullLogger.getInstance(),
          )
          .first
      } finally {
        LbePass.defaultLevel = defaultLevel
      }
    val heads =
      xcfa.procedures
        .flatMap { it.locs }
        .mapNotNull { (it.metadata as? CMetaData)?.loopHead }
        .distinct()
        .sortedBy { it.loop.lineNumberStart }
    val expected =
      source
        .lines()
        .withIndex()
        .filter { "// loop" in it.value }
        .map { (index, line) ->
          index + 1 to line.substringAfter("// loop").trim().split(" ").filter { it.isNotEmpty() }
        }
    assertEquals(expected.map { it.first }, heads.map { it.loop.lineNumberStart })
    for ((head, variables) in heads.zip(expected.map { it.second })) {
      assertTrue(head.complete) { "Loop at ${head.loop.lineNumberStart} lost its head" }
      assertEquals(variables.toSet(), head.variablesAtGuard.keys)
    }
  }
}
