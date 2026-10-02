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

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * A global loop counter may be substituted into the unrolled copies only when no concurrent thread
 * can write it: a thread-creation loop over a file-scope `i` (`pthread_create(&t[i], …)`) needs the
 * substitution to give each handle a constant index, while a counter another procedure writes must
 * keep its symbolic value.
 */
class UnrollGlobalLoopVarTest {

  /** The counter's increments in the unrolled copies: substituted ones have folded to a literal. */
  private fun unrolledIncrements(
    workerWritesCounter: Boolean,
    loopIsInInitProcedure: Boolean = true,
  ): List<AssignStmt<*>> {
    val builder = XcfaBuilder("")
    builder.global {
      "g" type Int() init "0"
      "other" type Int() init "0"
    }
    val main =
      builder.procedure("main") {
        (init to "L1") { "g".assign("0") }
        ("L1" to "L2") {
          assume("(< g 2)")
          "g".assign("(+ g 1)")
        }
        ("L2" to "L1") { skip() }
        ("L1" to final) { assume("(= g 2)") }
      }
    val worker =
      builder.procedure("worker") {
        (init to final) { (if (workerWritesCounter) "g" else "other").assign("5") }
      }
    builder.addEntryPoint(if (loopIsInInitProcedure) main.builder else worker.builder, listOf())

    val result =
      UnrollPass(substituteLoopVar = true, parseContext = ParseContext()).runChecked(main.builder)

    return result
      .getEdges()
      .filter { it.source.name != "main_init" }
      .flatMap { it.label.getFlatLabels() }
      .mapNotNull { (it as? StmtLabel)?.stmt as? AssignStmt<*> }
      .filter { it.varDecl.name == "g" }
  }

  @Test
  fun aCounterNoOtherProcedureWritesIsSubstituted() {
    val increments = unrolledIncrements(workerWritesCounter = false)
    assertEquals(2, increments.size, "the loop should have been unrolled twice")
    assertTrue(
      increments.all { it.expr is IntLitExpr },
      "each copy should carry the counter's constant value, got ${increments.map { it.expr }}",
    )
  }

  /** Only an init procedure is known to run once; any other may be a thread entry started twice. */
  @Test
  fun aCounterInAProcedureThatMayRunConcurrentlyIsNotSubstituted() {
    val increments = unrolledIncrements(workerWritesCounter = false, loopIsInInitProcedure = false)
    assertEquals(2, increments.size, "the loop should still have been unrolled twice")
    assertTrue(
      increments.none { it.expr is IntLitExpr },
      "a counter in a possibly concurrent procedure must keep its symbolic value, " +
        "got ${increments.map { it.expr }}",
    )
  }

  @Test
  fun aCounterAnotherProcedureWritesIsNotSubstituted() {
    val increments = unrolledIncrements(workerWritesCounter = true)
    assertEquals(2, increments.size, "the loop should still have been unrolled twice")
    assertTrue(
      increments.none { it.expr is IntLitExpr },
      "a concurrently written counter must keep its symbolic value, got ${increments.map { it.expr }}",
    )
  }
}
