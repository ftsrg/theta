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
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * `{ .field = v }` / `{ [i] = v }` used to be rejected outright ("Initializer list designators not
 * yet implemented" -- the aws-c-common cluster). The frontend now resolves each designator to its
 * element position and every consumer places elements by that position, C-style: a designator sets
 * the slot, each element advances it.
 */
class DesignatedInitializerTest {

  private fun writeOffsets(src: String): Set<String> {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val offsets = mutableSetOf<String>()
    fun visit(label: XcfaLabel) {
      when (label) {
        is SequenceLabel -> label.labels.forEach { visit(it) }
        is StmtLabel -> {
          val stmt = label.stmt
          if (stmt is MemoryAssignStmt<*, *, *>) offsets.add(stmt.deref.offset.toString())
        }
        else -> {}
      }
    }
    xcfa.procedures.forEach { proc -> proc.edges.forEach { visit(it.label) } }
    return offsets
  }

  @Test
  fun arrayIndexDesignatorPicksTheSlot() {
    val offsets =
      writeOffsets(
        """
        int a[4] = { [2] = 7 };
        int main() {
          if (a[2] != 7) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    assertTrue("2" in offsets, "the [2] designator must write element 2, got offsets: $offsets")
  }

  @Test
  fun fieldDesignatorPicksTheField() {
    val offsets =
      writeOffsets(
        """
        struct P { int x; int y; };
        struct P p = { .y = 3 };
        int main() {
          if (p.y != 3) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    assertTrue("1" in offsets, "the .y designator must write field 1, got offsets: $offsets")
  }

  @Test
  fun designatorAdvancesTheRunningPosition() {
    // `{ [2] = 7, 8 }` places 8 at index 3.
    val offsets =
      writeOffsets(
        """
        int a[5] = { [2] = 7, 8 };
        int main() {
          if (a[3] != 8) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    assertTrue(
      "2" in offsets && "3" in offsets,
      "elements must land at 2 and 3, got offsets: $offsets",
    )
  }

  @Test
  fun localStructDesignatedInitializer() {
    val offsets =
      writeOffsets(
        """
        struct P { int x; int y; };
        int main() {
          struct P q = { .y = 4 };
          if (q.y != 4) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    assertTrue("1" in offsets, "the .y designator must write field 1, got offsets: $offsets")
  }
}
