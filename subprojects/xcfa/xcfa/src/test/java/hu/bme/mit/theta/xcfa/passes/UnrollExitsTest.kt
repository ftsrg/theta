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

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class UnrollExitsTest {

  private val loopKey = UnrollExits.key(UnrollExits.Kind.LOOP, "main", "L1")

  /** A loop whose trip count depends on two variables, so it can only be force unrolled. */
  private fun unrolled(
    bound: Int,
    markExits: Boolean = true,
    cutBounds: Map<String, Int> = emptyMap(),
  ): XcfaProcedureBuilder {
    val builder =
      XcfaBuilder("").also {
        it.global {
          "x" type Int() init "0"
          "y" type Int() init "0"
        }
      }
    val procedure =
      builder
        .procedure("main") {
          (init to "L1") { "x".assign("0") }
          ("L1" to "L2") {
            assume("(< x y)")
            "x".assign("(+ x 1)")
          }
          ("L2" to "L1") { skip() }
          ("L1" to final) { assume("(>= x y)") }
        }
        .builder
    return UnrollPass(bound, cutBounds = cutBounds, markUnrollExits = markExits)
      .runChecked(procedure)
  }

  private fun XcfaProcedureBuilder.exits() = getLocs().filter { UnrollExits.keyOf(it) != null }

  @Test
  fun forcedUnrollLeadsTheNextIterationIntoAnExit() {
    val procedure = unrolled(2)
    assertTrue(procedure.unsafeUnrollUsed)
    val exit = procedure.exits().single()
    assertEquals(loopKey, UnrollExits.keyOf(exit))
    // the exit is reached exactly when the loop condition holds once more
    val labels = exit.incomingEdges.single().getFlatLabels()
    assertEquals(1, labels.size)
    assertTrue((labels.single() as StmtLabel).stmt is AssumeStmt)
    assertEquals(2, procedure.getLocs().count { it.name.startsWith("L2_loop") })
  }

  @Test
  fun noExitsUnlessAsked() {
    val procedure = unrolled(2, markExits = false)
    assertTrue(procedure.unsafeUnrollUsed)
    assertTrue(procedure.exits().isEmpty())
  }

  @Test
  fun cutBoundsOverrideTheDefaultPerKey() {
    val procedure = unrolled(2, cutBounds = mapOf(loopKey to 4))
    assertEquals(4, procedure.getLocs().count { it.name.startsWith("L2_loop") })
    assertEquals(loopKey, UnrollExits.keyOf(procedure.exits().single()))
  }

  @Test
  fun copiesOfAnExitKeepItsKey() {
    val name = UnrollExits.locationName(loopKey)
    val spliced = XcfaLocation(name + 42, metadata = EmptyMetaData)
    val perThread = XcfaLocation(name + 42 + "_3", metadata = EmptyMetaData)
    assertEquals(loopKey, UnrollExits.keyOf(spliced))
    assertEquals(loopKey, UnrollExits.keyOf(perThread))
    assertNull(UnrollExits.keyOf(XcfaLocation("L1", metadata = EmptyMetaData)))
    assertTrue(UnrollExits.kindOf(loopKey).deepenable)
  }
}
