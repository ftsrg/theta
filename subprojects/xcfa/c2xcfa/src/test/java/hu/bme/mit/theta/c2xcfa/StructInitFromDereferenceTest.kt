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
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * `struct S s = *p;` and `= o.field` used to be rejected ("Initializer type not handled for
 * structs") because only a plain variable (RefExpr) was accepted as the source of a struct-copy
 * initializer. A struct value is its base id wherever it is read from, so a Dereference source
 * copies the same way (the aws-c-common `struct aws_array_list tmp = *list_a;` cluster).
 */
class StructInitFromDereferenceTest {

  @Test
  fun structInitializedFromPointerDereference() {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        struct S { int a; int b; };
        int main() {
          struct S s;
          s.a = 1;
          struct S *p = &s;
          struct S t = *p;
          if (t.a != 1) { return 1; }
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

  @Test
  fun structInitializedFromMemberOfAnotherStruct() {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        struct In { int x; };
        struct Out { struct In in; };
        int main() {
          struct Out o;
          o.in.x = 2;
          struct In i = o.in;
          if (i.x != 2) { return 1; }
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
}
