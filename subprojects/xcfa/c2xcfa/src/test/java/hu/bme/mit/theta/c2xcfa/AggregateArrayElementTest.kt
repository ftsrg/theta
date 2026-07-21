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
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * An array whose elements are aggregates holds a base per element, exactly as a struct holds one
 * per field. Those bases used to be left unconstrained, so the solver could conflate two elements:
 * `a[1].x = 7` was readable through `a[0].x`, and a multi-dimensional array was rejected outright.
 * Each element now gets an object of its own.
 */
class AggregateArrayElementTest {

  private fun build(src: String) {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    assertTrue(xcfa.procedures.isNotEmpty(), "the program must build an XCFA")
  }

  /** Every memory write's (base, offset) pair, as strings. */
  private fun writes(src: String): List<Pair<String, String>> {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val found = mutableListOf<Pair<String, String>>()
    fun visit(label: XcfaLabel) {
      when (label) {
        is SequenceLabel -> label.labels.forEach { visit(it) }
        is StmtLabel ->
          (label.stmt as? MemoryAssignStmt<*, *, *>)?.let {
            found.add(it.deref.array.toString() to it.deref.offset.toString())
          }
        else -> {}
      }
    }
    xcfa.procedures.forEach { proc -> proc.edges.forEach { visit(it.label) } }
    return found
  }

  @Test
  fun aVariableLengthMatrixIsOneObjectWithNoStoredRowBases() {
    // The 2026-07-20 soundness regression, and the property that fixes it. A multi-dimensional VLA
    // is as contiguous as a constant one: `a[i][j]` must be `arrays[a][i*n + j]`, one object with
    // arithmetic offsets. It used to fall back to `arrays[arrays[a][i]][j]` -- a *stored* row base
    // that nothing ever writes, so the solver could pick the same base for two rows. Rows aliased,
    // and five array-patterns tasks plus init-non-constant-2-n-u reported a safe program unsafe.
    //
    // The signature to pin is therefore structural: no write may be addressed through a base that
    // is itself a dereference. That is exactly what a stored row base looks like.
    val w =
      writes(
        """
        extern short __VERIFIER_nondet_short();
        int main() {
          signed long long n = (signed long long) __VERIFIER_nondet_short();
          if (n <= 0) { return 0; }
          int a[n][n];
          a[1][0] = 7;
          a[0][0] = 1;
          return a[0][0];
        }
        """
          .trimIndent()
      )
    assertTrue(w.isNotEmpty(), "the writes must lower to memory assignments")
    assertTrue(
      w.none { (base, _) -> base.contains("deref") },
      "no row may live behind a stored base -- that is the aliasing bug; got $w",
    )
    assertEquals(1, w.map { it.first }.toSet().size, "every cell belongs to one object; got $w")
    // a[0][0] is offset 0; a[1][0] is offset 1*n, which stays symbolic rather than collapsing to a
    // constant -- if it folded to 0 the two rows would coincide again.
    assertTrue(w.any { it.second == "0" }, "a[0][0] sits at offset 0; got $w")
    assertTrue(
      w.any { it.second != "0" && it.second.contains("n") },
      "a[1][0] must be offset by the symbolic row length; got $w",
    )
  }

  /** The literal values a program's memory writes store, in program order, offset paired. */
  private fun writtenValues(src: String): List<Pair<String, String>> {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val found = mutableListOf<Pair<String, String>>()
    fun visit(label: XcfaLabel) {
      when (label) {
        is SequenceLabel -> label.labels.forEach { visit(it) }
        is StmtLabel ->
          (label.stmt as? MemoryAssignStmt<*, *, *>)?.let {
            found.add(it.deref.offset.toString() to ExprUtils.simplify(it.expr).toString())
          }
        else -> {}
      }
    }
    xcfa.procedures.forEach { proc -> proc.edges.forEach { visit(it.label) } }
    return found
  }

  @Test
  fun aFullyBracedMatrixInitializerFillsFlatCells() {
    // The 865-task unlock: a global multi-dimensional array with an initializer used to be refused
    // outright ("Not handling init expression of high dimsension array"), almost all
    // neural-network weight matrices and hardness. `int a[2][3] = {{1,2,3},{4,5,6}}` is one
    // contiguous object, so its values land in cells 0..5 in row-major order.
    val w = writtenValues("int a[2][3] = {{1,2,3},{4,5,6}};\nint main() { return a[0][0]; }")
    assertEquals(
      listOf("1", "2", "3", "4", "5", "6"),
      (0..5).map { off -> w.first { it.first == off.toString() }.second },
      "row-major flat fill; got $w",
    )
  }

  @Test
  fun aBraceElidedMatrixInitializerFillsTheSameCells() {
    // C allows the inner braces to be dropped: `{1,2,3,4,5,6}` fills `int a[2][3]` identically.
    // This is where the frontend's per-element position stops being a cell index -- element k is
    // row k, three cells wide -- so the flat walk descends by the running cursor instead.
    val w = writtenValues("int a[2][3] = {1,2,3,4,5,6};\nint main() { return a[0][0]; }")
    assertEquals(
      listOf("1", "2", "3", "4", "5", "6"),
      (0..5).map { off -> w.first { it.first == off.toString() }.second },
      "elided fill matches the braced one; got $w",
    )
  }

  @Test
  fun shortRowsInAMatrixInitializerZeroFillTheRest() {
    // A braced sub-object that runs out early still advances past its whole row, so
    // `{{1,2},{4}}` is 1,2,0,4,0,0 -- the untouched cells keep the zero C guarantees them.
    val w = writtenValues("int a[2][3] = {{1,2},{4}};\nint main() { return a[0][0]; }")
    assertEquals(
      listOf("1", "2", "0", "4", "0", "0"),
      (0..5).map { off -> w.first { it.first == off.toString() }.second },
      "short rows zero-fill to their row boundary; got $w",
    )
  }

  @Test
  fun deeplyBracedScalarLeavesAreUnwrapped() {
    // The canary regression the initializer change first caused. A struct of structs initialized
    // with nested braces bottoms out at scalar leaves that are themselves braced -- the kernel
    // headers write `{{{{{0U}}}}}`. Once nested braces build real nested lists (they used to
    // collapse to one UnsupportedInitializer), a scalar leaf arrives wrapped, and asking a list for
    // its single `.expression` throws. It must be unwrapped instead. `int x = {{5}}` is the crux.
    assertDoesNotThrow {
      build(
        """
        struct Inner { int v; };
        struct Outer { struct Inner in; int tag; };
        struct Outer o = { { {5} }, 7 };
        int over = {{9}};
        int main() { return o.in.v + o.tag + over; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aThreeDimensionalInitializerFlattensToo() {
    // The walk is depth-first, so it generalises past two dimensions. `int a[2][2][2]` fully
    // braced fills cells 0..7 with 1..8 in order.
    val w =
      writtenValues(
        "int a[2][2][2] = {{{1,2},{3,4}},{{5,6},{7,8}}};\nint main() { return a[0][0][0]; }"
      )
    assertEquals(
      (1..8).map { it.toString() },
      (0..7).map { off -> w.first { it.first == off.toString() }.second },
      "3-D initializer flattens depth-first; got $w",
    )
  }

  @Test
  fun structElementsAreInlineCellsOfTheArray() {
    // `struct S a[3]` with a two-cell S is six cells of one object: a[0].x is offset 0, a[1].x is
    // offset 2, a[2].y is offset 5. Elements used to be separate objects, one alloca each, whose
    // bases had to be written at the declaration.
    val w =
      writes(
        """
        struct S { int x; int y; };
        int main() {
          struct S a[3];
          a[0].x = 1;
          a[1].x = 7;
          a[2].y = 9;
          return a[0].x;
        }
        """
          .trimIndent()
      )
    assertEquals(1, w.map { it.first }.toSet().size, "all cells belong to the array itself; got $w")
    assertTrue(
      w.none { (base, _) -> base.contains("deref") },
      "no element may live behind a stored base; got $w",
    )
    assertEquals(listOf("0", "2", "5"), w.map { it.second }, "flat element offsets; got $w")
  }

  @Test
  fun aHugeStructArrayIsStillPreciseAndCostsNoAllocations() {
    // The point of the change. One alloca per element does not scale -- the benchmarks contain
    // `S a[1000000]` -- so above a 1024 cap the element bases were simply left unwritten, and the
    // solver could equate a[0] with a[1500]: the same conflation that produced the multi-dim VLA
    // false alarms, just harder to trigger. Offsets need no allocation, so the cap is gone.
    val w =
      writes(
        """
        struct S { int x; int y; };
        int main() {
          struct S a[2000];
          a[0].x = 1;
          a[1500].x = 7;
          return a[0].x;
        }
        """
          .trimIndent()
      )
    assertEquals(1, w.map { it.first }.toSet().size, "one object; got $w")
    assertEquals(listOf("0", "3000"), w.map { it.second }, "1500 * 2 cells in; got $w")
  }

  @Test
  fun anArrayOfArraysOfStructsScalesByCellsNotElements() {
    // The trap in the flat model: a row of `struct S a[2][3]` with a two-cell S is *six* cells
    // wide, not three. Scaling a row by its element count would land a[1] in the middle of row 0.
    // a[1][2].y = (1*6) + (2*2) + 1 = 11.
    val w =
      writes(
        """
        struct S { int x; int y; };
        int main() {
          struct S a[2][3];
          a[1][2].y = 7;
          return a[1][2].y;
        }
        """
          .trimIndent()
      )
    assertTrue(w.any { it.second == "11" }, "a[1][2].y is cell 11; got $w")
  }

  @Test
  fun aStructIsCopiedToAndFromAnArrayElement() {
    // An element is now an offset into the array rather than a variable, so both directions of
    // `t = a[i]` / `a[i] = t` had to keep working. `t = a[1]` in particular looks like pointer
    // arithmetic (`a + 1*k`) and was briefly rewritten to `t = &a[1]`, aliasing the two.
    val from =
      writes(
        """
        struct S { int x; int y; };
        int main() { struct S a[3]; struct S t; a[1].x = 7; t = a[1]; return t.x; }
        """
          .trimIndent()
      )
    assertTrue(
      from.any { it.first.contains("t") && it.second == "0" },
      "t receives its own copy of the element's cells; got $from",
    )
    assertTrue(
      from.any { it.first.contains("t") && it.second == "1" },
      "the copy is field by field, not a shared base; got $from",
    )

    val into =
      writes(
        """
        struct S { int x; int y; };
        int main() { struct S a[3]; struct S t; t.x = 7; a[2] = t; return a[2].x; }
        """
          .trimIndent()
      )
    assertTrue(
      into.any { it.first.contains("a") && it.second == "4" },
      "a[2] starts at cell 4 and is written field by field; got $into",
    )
  }

  @Test
  fun anElementWithANestedAggregateStillGetsItsSubobject() {
    // A nested struct field is still stored as a base id, so it needs allocating -- but into the
    // element's *flat* cell (element 1's `in` sits at cell 1*2 + 1 = 3), not into a per-element
    // object that no longer exists.
    val w =
      writes(
        """
        struct Inner { int p; int q; };
        struct Outer { int x; struct Inner in; };
        int main() {
          struct Outer a[2];
          a[0].x = 1;
          a[1].in.p = 7;
          return a[1].in.p;
        }
        """
          .trimIndent()
      )
    assertTrue(
      w.any { it.first.contains("deref") },
      "the nested Inner keeps a base of its own; got $w",
    )
    assertTrue(
      w.any { !it.first.contains("deref") && it.second == "3" },
      "element 1's nested base is written to flat cell 3; got $w",
    )
  }

  @Test
  fun structArraysBuildUnderBothEncodings() {
    for (arithmetic in listOf(ArithmeticType.efficient, ArithmeticType.bitvector)) {
      val parseContext = ParseContext()
      parseContext.arithmetic = arithmetic
      assertDoesNotThrow({
        getXcfaFromC(
          """
          extern int __VERIFIER_nondet_int();
          struct S { int x; int y; };
          int main() {
            struct S a[8];
            int i = __VERIFIER_nondet_int();
            if (i < 0 || i >= 8) { return 0; }
            a[i].y = 7;
            return a[i].y;
          }
          """
            .trimIndent()
            .byteInputStream(),
          parseContext,
          false,
          XcfaProperty(ErrorDetection.ERROR_LOCATION),
          NullLogger.getInstance(),
        )
      }, "a struct array indexed symbolically must build under $arithmetic")
    }
  }

  @Test
  fun aConstantMatrixStillFoldsToLiteralOffsets() {
    // The control: making the row length symbolic must not disturb the constant case, which still
    // has to fold to plain literals (`int a[2][3]`: a[1][0] is offset 3).
    val w =
      writes(
        """
        int main() {
          int a[2][3];
          a[1][0] = 7;
          a[0][0] = 1;
          return a[0][0];
        }
        """
          .trimIndent()
      )
    assertEquals(1, w.map { it.first }.toSet().size, "one object; got $w")
    assertTrue(w.any { it.second == "3" }, "a[1][0] folds to the literal offset 3; got $w")
    assertTrue(w.any { it.second == "0" }, "a[0][0] is offset 0; got $w")
  }

  @Test
  fun aVariableLengthMatrixKeepsItsRowsApartAcrossEncodings() {
    // The same shape has to build under bitvector arithmetic too, where the offset is Bv rather
    // than Int -- the multiply and add are typed differently there and have unified badly before.
    for (arithmetic in listOf(ArithmeticType.efficient, ArithmeticType.bitvector)) {
      val parseContext = ParseContext()
      parseContext.arithmetic = arithmetic
      assertDoesNotThrow({
        getXcfaFromC(
          """
          extern short __VERIFIER_nondet_short();
          int main() {
            signed long long n = (signed long long) __VERIFIER_nondet_short();
            if (n <= 0) { return 0; }
            int a[n][n];
            a[1][2] = 7;
            return a[1][2];
          }
          """
            .trimIndent()
            .byteInputStream(),
          parseContext,
          false,
          XcfaProperty(ErrorDetection.ERROR_LOCATION),
          NullLogger.getInstance(),
        )
      }, "a VLA matrix must build under $arithmetic")
    }
  }

  @Test
  fun multiDimensionalArrayBuilds() {
    // Used to fail outright: "Not handling init expression of high dimsension array".
    assertDoesNotThrow {
      build(
        """
        int main() {
          int a[3][4];
          a[0][0] = 1;
          a[1][2] = 7;
          if (a[0][0] != 1) { return 1; }
          if (a[1][2] != 7) { return 2; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun arrayOfStructsKeepsItsElementsApart() {
    // Writing one element must not be visible through another.
    assertDoesNotThrow {
      build(
        """
        struct S { int x; int y; };
        int main() {
          struct S a[3];
          a[0].x = 1;
          a[1].x = 7;
          if (a[0].x != 1) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun variableLengthArrayStillBuilds() {
    // A VLA has no constant element count, so there is nothing to allocate per element -- that
    // has to be an answer rather than an error (it used to throw "Only IntLit and BvLit ...").
    assertDoesNotThrow {
      build(
        """
        extern int __VERIFIER_nondet_int();
        int main() {
          unsigned int n = 4;
          int a[n];
          for (unsigned int j = 0; j < n; j++) { a[j] = __VERIFIER_nondet_int(); }
          return a[0];
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aPointerViewAddressesTheSameStorageAsTheDeclaredArray() {
    // The point of laying a multi-dimensional array out contiguously: `int a[3][4]` and an
    // `int (*)[4]` over it must name the same cells, in both directions. Row objects would not --
    // and the neural-network benchmarks reach their weights exactly this way, by casting a flat
    // buffer to `float (*)[N]`.
    assertDoesNotThrow {
      build(
        """
        int main() {
          int a[3][4];
          int (*A)[4] = a;
          a[1][2] = 7;
          if (A[1][2] != 7) { return 1; }
          A[2][3] = 9;
          if (a[2][3] != 9) { return 2; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun anArrayOfStructsAboveTheCapStillBuilds() {
    // One allocation per element does not scale -- the benchmarks contain `S a[1000000]` -- so
    // above the cap the elements are left sharing a base instead. Build, don't hang.
    assertDoesNotThrow {
      build(
        """
        struct S { int x; int y; };
        int main() { struct S a[2000]; a[0].x = 1; return a[0].x != 1; }
        """
          .trimIndent()
      )
    }
  }
}
