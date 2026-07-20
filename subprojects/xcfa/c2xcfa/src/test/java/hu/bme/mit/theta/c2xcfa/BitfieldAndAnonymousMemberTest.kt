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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * A single bitfield or anonymous member used to kill the whole struct's field list (the builder
 * threw, the caller swallowed it, and every later member lookup failed or mis-resolved). Bitfields
 * are now regular fields of their base type, unnamed bitfields are padding without a field slot,
 * and C11 anonymous struct/union members get a synthetic field that member lookup flattens
 * through.
 */
class BitfieldAndAnonymousMemberTest {

  private fun writeDerefs(src: String): List<Dereference<*, *, *>> {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val found = mutableListOf<Dereference<*, *, *>>()
    fun visit(label: XcfaLabel) {
      when (label) {
        is SequenceLabel -> label.labels.forEach { visit(it) }
        is StmtLabel -> {
          val stmt = label.stmt
          if (stmt is MemoryAssignStmt<*, *, *>) found.add(stmt.deref)
        }
        else -> {}
      }
    }
    xcfa.procedures.forEach { proc -> proc.edges.forEach { visit(it.label) } }
    return found
  }

  @Test
  fun consecutiveBitfieldsShareAStorageUnit() {
    // lo:4 and hi:4 fit one 32-bit unit, so they share cell 0 and `count` follows at cell 1 --
    // the cell count then matches the packed byte size a program allocates for (batch 45).
    val derefs =
      writeDerefs(
        """
        struct flags { unsigned lo : 4; unsigned hi : 4; int count; };
        int main() {
          struct flags f;
          f.lo = 3;
          f.count = 5;
          if (f.lo != 3 || f.count != 5) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    assertTrue(derefs.isNotEmpty(), "member writes must lower to memory assignments")
    val offsets = derefs.map { it.offset.toString() }.toSet()
    assertTrue("0" in offsets, "f.lo lives in the packed unit at cell 0")
    assertTrue("1" in offsets, "f.count follows the bitfield unit at cell 1")
    assertFalse("2" in offsets, "the two bitfields must not each take their own cell")
  }

  @Test
  fun unnamedBitfieldIsPaddingWithoutAFieldSlot() {
    val derefs =
      writeDerefs(
        """
        struct padded { int a; int : 3; int b; };
        int main() {
          struct padded p;
          p.a = 1;
          p.b = 2;
          if (p.a != 1 || p.b != 2) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    val offsets = derefs.map { it.offset.toString() }.toSet()
    assertTrue("0" in offsets && "1" in offsets, "a and b must be fields 0 and 1")
    assertFalse("2" in offsets, "the unnamed bitfield must not occupy a field slot")
  }

  @Test
  fun packedBitfieldsDoNotClobberEachOther() {
    // The soundness property packing must not break: b, c and d share one cell, so each write has
    // to splice only its own bits. A whole-cell write would make the reads interfere.
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        struct A { unsigned char a; unsigned char b:2; unsigned char c:2; unsigned char d:4; };
        int main() {
          struct A x;
          x.b = 2;
          x.c = 3;
          x.d = 4;
          if (x.b != 2) { return 1; }
          if (x.c != 3) { return 2; }
          if (x.d != 4) { return 3; }
          return 0;
        }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    assertTrue(xcfa.procedures.isNotEmpty(), "the program must build an XCFA")
  }

  /** The values a program's memory assignments store, simplified to literals where possible. */
  private fun storedValues(src: String): List<String> {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val found = mutableListOf<String>()
    fun visit(label: XcfaLabel) {
      when (label) {
        is SequenceLabel -> label.labels.forEach { visit(it) }
        is StmtLabel -> {
          val stmt = label.stmt
          if (stmt is MemoryAssignStmt<*, *, *>) found.add(ExprUtils.simplify(stmt.expr).toString())
        }
        else -> {}
      }
    }
    xcfa.procedures.forEach { proc -> proc.edges.forEach { visit(it.label) } }
    return found
  }

  @Test
  fun braceInitializerFoldsPackedBitfieldsIntoOneCell() {
    // The batch-46 regression: once bitfields pack, an initializer element is a *member* index,
    // not a cell index, so `{1, 2}` is one cell holding 1 | (2 shl 4) == 0x21 == 33. The old code
    // refused outright ("Brace initializer for a struct with packed bitfields is not supported"),
    // which cost 36 benchmark tasks; writing 1 and 2 into two separate cells would be worse still.
    val values =
      storedValues(
        """
        struct F { unsigned a : 4; unsigned b : 4; };
        struct F g = {1, 2};
        int main() { return g.a != 1 || g.b != 2; }
        """
          .trimIndent()
      )
    assertTrue("33" in values, "a=1 and b=2 must fold into a single cell 0x21, got $values")
  }

  @Test
  fun designatedInitializerLandsInItsOwnBits() {
    // `.b = 2` names the second 4-bit field, so the cell is 2 shl 4 == 32 and `a` keeps its zero.
    val values =
      storedValues(
        """
        struct F { unsigned a : 4; unsigned b : 4; };
        struct F g = {.b = 2};
        int main() { return g.b != 2; }
        """
          .trimIndent()
      )
    assertTrue("32" in values, "designated .b=2 must occupy the high nibble, got $values")
  }

  @Test
  fun initializerSpanningAPackedUnitAndAPlainMember() {
    // Mixed layout: a and b share cell 0, count is cell 1. The element-to-cell mapping shifts,
    // which is exactly what made the naive field-indexed iteration wrong.
    val values =
      storedValues(
        """
        struct F { unsigned a : 4; unsigned b : 4; int count; };
        struct F g = {1, 2, 7};
        int main() { return g.count != 7; }
        """
          .trimIndent()
      )
    assertTrue("33" in values, "the two bitfields fold into cell 0 as 0x21, got $values")
    assertTrue("7" in values, "count keeps its own cell and its own value, got $values")
  }

  @Test
  fun anonymousUnionMemberIsFlattened() {
    // `s.a` reaches `a` through the anonymous union: one access for the synthetic member
    // (its stored base), then one for `a` within it -- the same shape as a named nested struct.
    val derefs =
      writeDerefs(
        """
        struct S { union { int a; int b; }; int c; };
        int main() {
          struct S s;
          s.a = 1;
          s.c = 2;
          if (s.a != 1 || s.c != 2) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    assertTrue(derefs.isNotEmpty(), "member writes must lower to memory assignments")
    assertTrue(
      derefs.any { it.array is Dereference<*, *, *> },
      "s.a must go through the anonymous member's base (a two-step access)",
    )
  }
}
