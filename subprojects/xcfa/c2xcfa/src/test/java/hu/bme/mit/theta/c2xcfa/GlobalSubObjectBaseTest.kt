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
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * A struct-typed field of a global struct gets exactly one compile-time base, and it is the one
 * [ParseContext.subObjectBaseAt] reports -- the data-race check resolves `g.in.x` through it.
 */
class GlobalSubObjectBaseTest {

  @Test
  @DisplayName("a global's nested struct field is given one base, the recorded one")
  fun nestedFieldBaseIsMintedOnce() {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        struct In { int x; int y; };
        struct Out { int a; struct In in; struct In in2; } g;
        int main(void) { return g.in.x + g.in2.y; }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    // The passes fold the constant bases into the dereferences, so a cell shows up as
    // `(deref <base> <cell>)` with both operands literal; keep the cells that hold a sub-object.
    val baseCellWrites =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<StmtLabel>()
        .map { it.stmt }
        .filterIsInstance<MemoryAssignStmt<*, *, *>>()
        .filter {
          val array = it.deref.array.asConstantBigInteger()
          val offset = it.deref.offset.asConstantBigInteger()?.toInt()
          array != null && parseContext.subObjectBaseAt(array, offset) != null
        }
        .groupBy {
          it.deref.array.asConstantBigInteger()!! to it.deref.offset.asConstantBigInteger()!!
        }
    assertEquals(2, baseCellWrites.size, "g.in and g.in2 are the only base cells: $baseCellWrites")
    for ((cell, writes) in baseCellWrites) {
      assertEquals(1, writes.size, "cell $cell must be written once (got $writes)")
      assertEquals(
        parseContext.subObjectBaseAt(cell.first, cell.second.toInt()),
        writes.single().expr.asConstantBigInteger(),
        "cell $cell must hold the recorded sub-object base",
      )
    }
  }

  @Test
  @DisplayName("the cells of a nested struct field that is never read are not initialized")
  fun unreadNestedFieldIsNotInitialized() {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        struct In { int x; int y; };
        struct Out { int a; struct In in; } g;
        int main(void) { return g.a; }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val inBase = parseContext.subObjectBaseAt(BigInteger.ONE, 1)
    assertNotNull(inBase)
    val writes =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<StmtLabel>()
        .map { it.stmt }
        .filterIsInstance<MemoryAssignStmt<*, *, *>>()
    // g.in's base is not stored, so a write through its cell would land at an unknown address.
    assertTrue(
      writes.none {
        it.deref.array is Dereference<*, *, *> || it.deref.array.asConstantBigInteger() == inBase
      },
      "g.in is never read, so nothing may be written to it: $writes",
    )
  }
}
