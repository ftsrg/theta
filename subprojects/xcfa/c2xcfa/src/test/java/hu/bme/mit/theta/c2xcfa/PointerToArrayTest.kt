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
 * `T (*p)[N]` (a pointer to an array) and `T *p[N]` (an array of pointers) reach the declarator
 * with the same star and dimension counts and are told apart only by the order they arrived in.
 * Getting that wrong is silent: an earlier attempt that applied the star unconditionally turned
 * every array of pointers into a pointer to an array, which still builds and still verifies --
 * just against the wrong object. Both forms are pinned here.
 */
class PointerToArrayTest {

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
  fun pointerToArrayIsSubscriptable() {
    // `(*p)[i]` used to fail as "Non-array expression used as array": the star was dropped, so p
    // was typed as the array itself and `*p` yielded an element with nothing left to subscript.
    assertDoesNotThrow {
      build(
        """
        int main() {
          int a[4];
          int (*p)[4] = &a;
          (*p)[2] = 7;
          if ((*p)[2] != 7) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun pointerToArrayAliasesThePointee() {
    // The star binds outside the dimensions, so p points *at* a -- a write through p must be
    // visible in a. (`*p` denotes the array object itself, not a cell read of its first element.)
    assertDoesNotThrow {
      build(
        """
        int main() {
          int a[4];
          int (*p)[4] = &a;
          (*p)[2] = 7;
          if (a[2] != 7) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun arrayOfPointersKeepsItsElementStar() {
    // The other binding: here the star belongs to the element type, so q is an array of pointers.
    assertDoesNotThrow {
      build(
        """
        int main() {
          int x = 1, y = 2;
          int *q[2];
          q[0] = &x;
          q[1] = &y;
          if (*q[1] != 2) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun pointerToArrayOfUnspecifiedSize() {
    // The TDX/kernel shape: `T (*dest)[]` with the size left open, subscripted through `(*dest)[i]`.
    assertDoesNotThrow {
      build(
        """
        void fill(unsigned long (*dest)[], int n) {
          for (int i = 0; i < n; i++) { (*dest)[i] = 0; }
        }
        int main() { unsigned long a[4]; fill(&a, 4); return a[0] != 0; }
        """
          .trimIndent()
      )
    }
  }
}
