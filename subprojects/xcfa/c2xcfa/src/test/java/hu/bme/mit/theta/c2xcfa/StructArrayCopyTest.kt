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
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * A struct's array field is copied element by element, not by sharing the array.
 *
 * A struct field that is an array holds a base id, just like a struct-typed field. Copying a struct
 * used to assign that base straight across, so the destination's array *was* the source's -- writing
 * one showed up in the other. C copies the elements, so the destination keeps the array it was
 * allocated and each element is copied into it: `arrays[dst_a][k] := arrays[src_a][k]`.
 *
 * Those element copies are the fingerprint: a write per element that reads one array and writes a
 * *different* one. A three-element field yields three; without the fix there is one base assignment
 * and no element copy at all.
 */
class StructArrayCopyTest {

  /** Copies that read an element of one array and write the same element of another. */
  private fun crossArrayElementCopies(body: String): List<MemoryAssignStmt<*, *, *>> {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        struct T { int a[3]; };
        int main(void) {
          struct T x; struct T y;
          x.a[0] = 1; x.a[1] = 2; x.a[2] = 3;
          $body
          return y.a[0];
        }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    return xcfa.procedures
      .flatMap { it.edges }
      .flatMap { it.getFlatLabels() }
      .filterIsInstance<StmtLabel>()
      .map { it.stmt }
      .filterIsInstance<MemoryAssignStmt<*, *, *>>()
      .filter { stmt ->
        // arrays[dst_a][k] := arrays[src_a][k]: element cells of two *different* arrays
        val toArray = (stmt.deref as? Dereference<*, *, *>)?.array
        val fromArray = (stmt.expr as? Dereference<*, *, *>)?.array
        toArray is Dereference<*, *, *> &&
          fromArray is Dereference<*, *, *> &&
          toArray.array != fromArray.array
      }
  }

  @Test
  @DisplayName("a struct's array field is copied element by element")
  fun arrayFieldCopiedElementwise() {
    val copies = crossArrayElementCopies("y = x;")
    assertEquals(
      3,
      copies.size,
      "`y = x` must copy the three array elements into y's own array (copies: $copies)",
    )
  }

  @Test
  @DisplayName("no element copy without an assignment")
  fun noAssignmentNoCopy() {
    assertEquals(0, crossArrayElementCopies("").size, "there is no struct copy here")
  }
}
