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
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
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
