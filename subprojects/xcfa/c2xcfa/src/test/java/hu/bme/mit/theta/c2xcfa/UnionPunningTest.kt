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
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Test

/**
 * A union member access is allowed when the members occupy their shared cell identically -- same
 * SMT sort, width, and signedness -- and rejected (as unsupported punning) otherwise. Requiring
 * identical C classes was too strict and blocked the pervasive `union { void *ptr; size_t i; }`
 * idiom; relaxing it must not, however, let width- or sign-mismatched members silently alias.
 */
class UnionPunningTest {

  private fun build(src: String) {
    val parseContext = ParseContext()
    getXcfaFromC(
      src.byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
  }

  @Test
  fun pointerAndPointerWidthUnsignedAlias() {
    assertDoesNotThrow {
      build(
        """
        union U { void *ptr; unsigned long i; };
        int main() {
          union U u;
          int x = 5;
          u.ptr = &x;
          if (u.i == 0) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun signedAndUnsignedOfSameWidthDoNotAlias() {
    // int/unsigned share the Int sort under integer arithmetic; aliasing them would lose the sign
    // reinterpretation, so this must still be rejected.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        union U { int s; unsigned u; };
        int main() { union U x; x.u = 1; return x.s; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun differentWidthMembersDoNotAlias() {
    // int/char share the Int sort under integer arithmetic but differ in width; u.i = 300; u.c
    // must be 44, not 300, so aliasing is rejected.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        union U { int i; char c; };
        int main() { union U x; x.i = 300; return x.c; }
        """
          .trimIndent()
      )
    }
  }
}
