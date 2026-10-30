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
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.api.assertThrows

/** `ByteViewPass` asks for the bytes model exactly when a known object is read byte by byte. */
class ByteViewPassTest {

  private fun build(src: String) {
    getXcfaFromC(
      (PRELUDE + src).byteInputStream(),
      ParseContext(),
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
  }

  @Test
  fun byteViewOfAStructAfterMemsetNeedsBytes() {
    assertThrows<RequiresByteAddressedMemoryException> {
      build(
        """
        struct S { long a; long b; };
        int main() {
          struct S s;
          memset(&s, 0, sizeof s);
          const unsigned char *p = (const unsigned char *)&s;
          if (p[2]) reach_error();
          return 0;
        }
        """
      )
    }
  }

  @Test
  fun byteViewThroughAVoidPointerParameterNeedsBytes() {
    assertThrows<RequiresByteAddressedMemoryException> {
      build(
        """
        int zeroed(const void *buf, unsigned long n) {
          const unsigned char *p = buf;
          for (unsigned long i = 0; i < n; ++i) if (p[i]) return 0;
          return 1;
        }
        int main() {
          long x;
          memset(&x, 0, sizeof x);
          if (!zeroed(&x, sizeof x)) reach_error();
          return 0;
        }
        """
      )
    }
  }

  @Test
  fun charMemberCharArrayAndFieldReadsStayOnTheDefaultModel() {
    assertDoesNotThrow {
      build(
        """
        struct M { char c; int x; };
        struct P { void *next; void *prev; };
        int main() {
          struct M m; m.c = 1; m.x = 2;
          char *q = &m.c;
          if (*q != 1) reach_error();
          char buf[8];
          memset(buf, 0, sizeof buf);
          for (int i = 0; i < 8; ++i) if (buf[i]) reach_error();
          struct P n;
          memset(&n, 0, sizeof n);
          if (n.next || n.prev) reach_error();
          return 0;
        }
        """
      )
    }
  }

  private companion object {
    const val PRELUDE = "void reach_error(); void *memset(void *, int, unsigned long);\n"
  }
}
