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
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Test

/**
 * The byte-granular memory model (`--memory-model bytes`) lowers every memory access through
 * one-byte cells, so a wider scalar is the Concat of its bytes and struct/union members sit at their
 * real ObjectLayout byte offsets in the one byte array. These tests pin that the frontend keeps
 * *lowering* each construct under the bytes model -- cross-width punning, ABI-padded structs, nested
 * structs, arrays of structs, byte-array and pointer unions, bitfields, and the address of a
 * multi-byte union member (which the multi model refuses). The end-to-end verdicts against gcc are
 * checked separately by the analysis (STABLE portfolio) and are not re-run here; this is the cheap
 * guard that the bytes lowering does not regress to an exception.
 */
class BytesMemoryModelTest {

  private fun buildBytes(src: String) {
    val parseContext = ParseContext()
    parseContext.arithmetic = ArithmeticType.bitvector
    parseContext.memoryModel = MemoryModelType.bytes
    getXcfaFromC(
      src.byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
  }

  @Test
  fun crossWidthScalarPunningLowers() {
    assertDoesNotThrow {
      buildBytes(
        """
        int main() {
          unsigned long x = 0x1122334455667788UL;
          unsigned char *p = (unsigned char *) &x;
          return p[0] + p[7];
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun paddedStructMembersAndAByteViewLower() {
    // char a then int b: b lands at byte offset 4, past the padding -- a byte view reads it there.
    assertDoesNotThrow {
      buildBytes(
        """
        struct S { unsigned char a; unsigned int b; };
        int main() {
          struct S s; s.a = 1; s.b = 0x01020304;
          unsigned char *p = (unsigned char *) &s;
          return p[4];
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun nestedStructAndArrayOfStructsLower() {
    assertDoesNotThrow {
      buildBytes(
        """
        struct Inner { int x; int y; };
        struct Outer { int head; struct Inner in; };
        struct P { int x; int y; };
        int main() {
          struct Outer o; o.in.x = 2; o.in.y = 3;
          struct P a[3]; a[1].x = 7; a[2].y = 9;
          return o.in.x + a[1].x + a[2].y;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun containerOfRoundTripsThroughOffsetof() {
    assertDoesNotThrow {
      buildBytes(
        """
        struct Node { int data; int key; };
        int main() {
          struct Node n; n.data = 7; n.key = 99;
          int *pk = &n.key;
          struct Node *back =
            (struct Node *) ((char *) pk - __builtin_offsetof(struct Node, key));
          return back->data;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun crossWidthUnionAndByteArrayUnionLower() {
    assertDoesNotThrow {
      buildBytes(
        """
        union U { unsigned long raw; unsigned int half; unsigned char bytes[8]; };
        int main() {
          union U u; u.raw = 0x0102030405060708UL;
          return u.half + u.bytes[0];
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun addressOfAMultiByteUnionMemberAndDerefThroughLowers() {
    // TDX barrier 9: the multi model refuses `&u.raw` for a multi-byte member; the bytes model gives
    // it a real byte address whose dereference reads the same bytes back.
    assertDoesNotThrow {
      buildBytes(
        """
        union U { unsigned long raw; unsigned char bytes[8]; };
        int main() {
          union U u; u.raw = 0x1122334455667788UL;
          unsigned long *p = &u.raw;
          return (int) *p;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun pointerStoredInAUnionAndReadThroughAnIntegerViewLowers() {
    assertDoesNotThrow {
      buildBytes(
        """
        union U { void *ptr; unsigned long bits; };
        int main() {
          int x = 42;
          union U u; u.ptr = &x;
          int *back = (int *) u.bits;
          return *back;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun bitfieldsReadWriteAndOverlayLower() {
    assertDoesNotThrow {
      buildBytes(
        """
        struct F { unsigned int a : 4; unsigned int b : 4; unsigned int c : 24; };
        union U { unsigned int raw; struct { unsigned int lo : 16; unsigned int hi : 16; }; };
        int main() {
          struct F f; f.a = 5; f.b = 10; f.c = 0x123456; f.a = 3;
          union U u; u.raw = 0xABCD1234;
          return f.a + f.b + u.lo + u.hi;
        }
        """
          .trimIndent()
      )
    }
  }
}
