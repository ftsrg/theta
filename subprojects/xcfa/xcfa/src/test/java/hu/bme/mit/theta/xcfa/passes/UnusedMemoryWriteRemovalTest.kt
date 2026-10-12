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

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

/** [UnusedVarPass] removes the writes to global objects that no read may reach. */
class UnusedMemoryWriteRemovalTest {

  private fun ParseContext.static(base: Int, union: Boolean = false, parent: Int? = null) = apply {
    recordStaticObject(base.toBigInteger(), union, parent?.toBigInteger())
  }

  /** The cells still written after the pass, in order. */
  private fun writtenCells(
    parseContext: ParseContext,
    property: ErrorDetection = ErrorDetection.ERROR_LOCATION,
    body: XcfaProcedureBuilderContext.() -> Unit,
  ): List<String> {
    val builder = XcfaBuilder("").procedure("main", body).builder
    val passes =
      listOf(
        NormalizePass(),
        DeterministicPass(),
        UnusedVarPass(NullLogger.getInstance(), XcfaProperty(property), parseContext),
      )
    val result = passes.fold(builder) { acc, pass -> pass.runChecked(acc) }
    return result.getEdges().sortedBy { it.source.name }.flatMap { writesIn(it.label) }
  }

  private fun writesIn(label: XcfaLabel): List<String> =
    when (label) {
      is SequenceLabel -> label.labels.flatMap(::writesIn)
      is NondetLabel -> label.labels.flatMap(::writesIn).sorted()
      is StmtLabel -> listOfNotNull((label.stmt as? MemoryAssignStmt<*, *, *>)?.deref?.toString())
      else -> listOf()
    }

  @Test
  fun unreadWritesToStaticObjectsAreRemoved() {
    val cells =
      writtenCells(ParseContext().static(1)) {
        (init to "L1") {
          "(deref 1 0 Int)".memassign("1")
          "(deref 1 1 Int)".memassign("2")
          "(deref 100 0 Int)".memassign("3")
        }
        ("L1" to final) { assume("(= (deref 1 0 Int) 1)") }
      }
    assertEquals(listOf("(deref 1 0 Int)", "(deref 100 0 Int)"), cells)
  }

  @Test
  fun aUnionIsKeptOrRemovedAsAWhole() {
    val parseContext = ParseContext().static(4, union = true).static(7, parent = 4)
    parseContext.static(10, union = true)
    val cells =
      writtenCells(parseContext) {
        (init to "L1") {
          "(deref 4 0 Int)".memassign("7")
          "(deref 7 1 Int)".memassign("2")
          "(deref 10 0 Int)".memassign("3")
        }
        ("L1" to final) { assume("(= (deref 7 0 Int) 0)") }
      }
    assertEquals(listOf("(deref 4 0 Int)", "(deref 7 1 Int)"), cells)
  }

  @Test
  fun writtenBasesAreForwardedIntoNestedAddresses() {
    val cells =
      writtenCells(ParseContext().static(1).static(7, parent = 1)) {
        "x" type Int()
        "p" type Int()
        (init to "L1") {
          "(deref 1 2 Int)".memassign("7")
          "(deref p 0 Int)".memassign("0")
          "(deref (deref 1 2 Int) 0 Int)".memassign("5")
          "x".assign("(deref (deref 1 2 Int) 1 Int)")
          assume("(= (deref (deref 1 2 Int) 3 Int) 0)")
        }
        ("L1" to final) { assume("(= x 6)") }
      }
    assertEquals(listOf("(deref p 0 Int)"), cells)
  }

  @Test
  fun writesInNondetBranchesAreRemovedUnderFlatAddressing() {
    val parseContext = ParseContext().static(1).static(2)
    parseContext.memoryModel = MemoryModelType.flat
    val cells =
      writtenCells(parseContext) {
        "m" type Int()
        (init to "L1") {
          nondet {
            sequence { "(deref 0 65536 Int)".memassign("1") }
            sequence { "(deref 0 131072 Int)".memassign("2") }
          }
        }
        ("L1" to final) {
          mutex_lock("m")
          assume("(= (deref 0 65536 Int) 1)")
        }
      }
    assertEquals(listOf("(deref 0 65536 Int)"), cells)
  }

  @Test
  fun everyWriteIsKeptAcrossAnUnknownCallee() {
    val cells =
      writtenCells(ParseContext().static(1)) {
        (init to "L1") { "(deref 1 0 Int)".memassign("1") }
        ("L1" to final) { "unknown"() }
      }
    assertEquals(listOf("(deref 1 0 Int)"), cells)
  }

  @Test
  fun everyWriteIsKeptWhenCheckingDataRaces() {
    val cells =
      writtenCells(ParseContext().static(1), ErrorDetection.DATA_RACE) {
        (init to final) { "(deref 1 0 Int)".memassign("1") }
      }
    assertEquals(listOf("(deref 1 0 Int)"), cells)
  }
}
