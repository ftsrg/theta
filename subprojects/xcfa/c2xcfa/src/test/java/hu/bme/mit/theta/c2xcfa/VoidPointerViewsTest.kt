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
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.api.assertThrows

class VoidPointerViewsTest {

  private fun build(src: String, parseContext: ParseContext = ParseContext()) {
    getXcfaFromC(
      src.trimIndent().byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
  }

  @Test
  fun structReachesCharViewThroughVoidParameter() {
    assertThrows<RequiresByteAddressedMemoryException> {
      build(
        """
        struct node { struct node *next; struct node *prev; };
        int zeroed(const void *buf, unsigned long n) {
          const unsigned char *b = (const unsigned char *)buf;
          for (unsigned long i = 0; i < n; ++i) if (b[i]) return 0;
          return 1;
        }
        int main() { struct node node; node.next = 0; node.prev = 0; return zeroed(&node, sizeof node); }
        """
      )
    }
  }

  @Test
  fun intReachesCharViewThroughVoidVariable() {
    assertThrows<RequiresByteAddressedMemoryException> {
      build(
        """
        int main() { unsigned int x = 1; void *v = &x; unsigned char *c = v; return c[0]; }
        """
      )
    }
  }

  @Test
  fun directCastOfStructToCharPointer() {
    assertThrows<RequiresByteAddressedMemoryException> {
      build(
        """
        struct S { int a; int b; };
        int main() { struct S s = {1, 2}; unsigned char *p = (unsigned char *)&s; return p[4]; }
        """
      )
    }
  }

  @Test
  fun separateVoidPointersKeepTheCellModel() {
    assertDoesNotThrow {
      build(
        """
        void *malloc(unsigned long);
        struct S { int a; };
        void *id(void *p) { return p; }
        int main() {
          char *s = malloc(4);
          struct S *p = malloc(sizeof *p);
          void *opaque = id(p);
          struct S *q = opaque;
          s[0] = 'a';
          return q->a + s[0];
        }
        """
      )
    }
  }

  @Test
  fun bytesModelIsNotChecked() {
    val parseContext = ParseContext()
    parseContext.memoryModel = ArchitectureConfig.MemoryModelType.bytes
    parseContext.arithmetic = ArchitectureConfig.ArithmeticType.bitvector
    assertDoesNotThrow {
      build(
        """
        int main() { unsigned int x = 1; void *v = &x; unsigned char *c = v; return c[0]; }
        """,
        parseContext,
      )
    }
  }
}
