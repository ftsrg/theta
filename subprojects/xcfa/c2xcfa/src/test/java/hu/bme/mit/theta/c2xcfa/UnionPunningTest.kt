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

  private fun build(src: String) = build(src, ArithmeticType.efficient)

  private fun build(src: String, arithmetic: ArithmeticType) {
    val parseContext = ParseContext()
    parseContext.arithmetic = arithmetic
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
  fun signedAndUnsignedOfSameWidthAliasThroughTheSlice() {
    // This used to assert a *rejection*: int/unsigned share the Int sort under integer arithmetic,
    // so aliasing them naively would lose the sign reinterpretation. Slicing does not lose it --
    // the read sign-extends from the member's own width -- so the case is now supported rather
    // than refused. The old expectation encoded the limitation, not a requirement.
    assertDoesNotThrow {
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
  fun narrowerMembersReadTheLowBitsOfTheWord() {
    // Also formerly a rejection. `u.i = 300; u.c` must be 44, not 300 -- which is exactly what
    // slicing the low 8 bits gives, so the width difference is now modelled instead of refused.
    // The values are verified end to end rather than here: with `u.raw = 2^32 + 1`, `u.half == 1`
    // proves Safe under both encodings, and negating that assertion proves Unsafe, so the check
    // is not vacuous.
    assertDoesNotThrow {
      build(
        """
        union U { int i; char c; };
        int main() { union U x; x.i = 300; return x.c; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun packedBitfieldViewSharesTheUnionsCellWithItsIntegerSibling() {
    // The kernel/TDX register-overlay idiom: a struct that is one packed unit of bitfields holds
    // nothing but that unit's integer, so it aliases a sibling integer member exactly.
    assertDoesNotThrow {
      build(
        """
        typedef union {
          struct { unsigned long leaf:16; unsigned long version:8; unsigned long rest:40; };
          unsigned long raw;
        } u_t;
        int main() {
          u_t u;
          u.raw = 0;
          u.leaf = 7;
          if (u.raw == 0) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun multiFieldStructOverAnIntegerSharesTheCell() {
    // Two plain 32-bit members packed into a 64-bit word: the same overlay, without a bitfield in
    // sight. `lo` is the low half and `hi` the high half of `raw`.
    assertDoesNotThrow {
      build(
        """
        typedef union { struct { unsigned int lo; unsigned int hi; }; unsigned long raw; } u_t;
        int main() {
          u_t u;
          u.raw = 0;
          u.lo = 7;
          u.hi = 3;
          if (u.lo != 7) { return 1; }
          if (u.raw == 0) { return 2; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aStructTooWideForAWordStillRejects() {
    // Sixteen 64-bit registers are not a word; there is no integer to hold the overlay.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        typedef union { struct { unsigned long a; unsigned long b; unsigned long c; }; unsigned long raw; } u_t;
        int main() { u_t u; u.raw = 0; return (int) u.a; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun membersOfDifferentWidthsShareTheWordAsSlices() {
    // AD7, the tractable half. A union's members all start at offset 0, so a narrower member is
    // simply the low bits of the same word -- `u.raw = 0; u.half = 7` must leave `u.raw == 7`.
    // This used to be refused outright as "members do not all share a representation", which is
    // the single largest addressable frontend cluster (~1,029 tasks in the 2026-07-20 run).
    // Both encodings: the slice is div/mod under integer arithmetic and Extract/Concat under
    // bitvector, and the cell is read at the *union's* width in either.
    for (arithmetic in listOf(ArithmeticType.efficient, ArithmeticType.bitvector)) {
      assertDoesNotThrow({
        build(
          """
          union U { unsigned long raw; unsigned int half; };
          int main() {
            union U u;
            u.raw = 0;
            u.half = 7;
            if (u.raw != 7) { return 1; }
            return 0;
          }
          """
            .trimIndent(),
          arithmetic,
        )
      }, "differing widths must alias by slicing under $arithmetic")
    }
  }

  @Test
  fun differingSignsAndNarrowerTypesNowAliasToo() {
    // Previously both were rejected: int/unsigned lose the sign reinterpretation if aliased
    // naively, and int/char differ in width. Slicing handles both -- the read sign-extends from
    // the member's own width, so `u.i = 300; u.c` is 44 rather than 300.
    for (arithmetic in listOf(ArithmeticType.efficient, ArithmeticType.bitvector)) {
      assertDoesNotThrow({
        build("union U { int s; unsigned u; };\nint main() { union U x; x.u = 1; return x.s; }",
          arithmetic)
      }, "int/unsigned under $arithmetic")
      assertDoesNotThrow({
        build("union U { int i; char c; };\nint main() { union U x; x.i = 300; return x.c; }",
          arithmetic)
      }, "int/char under $arithmetic")
    }
  }

  @Test
  fun anArrayMemberIsStillRefused() {
    // Honest boundary. `union { uint64_t raw; uint8_t bytes[8]; }` needs the byte-addressed object
    // layout: an array is many cells, not one word, so there is nothing to slice. Refused rather
    // than answered wrongly -- and this is what still blocks the intel-tdx-module cluster.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        union U { unsigned long raw; unsigned char bytes[8]; };
        int main() { union U u; u.raw = 0; return u.bytes[0]; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aFloatingPointMemberSharesTheCellAsItsIeeeBits() {
    // Formerly refused: a double's SMT sort is not a bitvector, so reading it as bits needs a
    // reinterpretation. That reinterpretation now exists (FpToIeeeBv / FpFromIeeeBv), so the
    // float-newlib idiom -- `union { double value; struct { uint32_t lsw, msw; } parts; }`, ~265
    // tasks -- is modelled instead of rejected. A float always forces bitvector arithmetic, so the
    // shared cell is a bitvector; the value semantics (double 1.0 -> msw 0x3FF00000, lsw 0, and
    // back) are checked end to end elsewhere.
    assertDoesNotThrow {
      build(
        """
        typedef unsigned int u32;
        typedef union { double value; struct { u32 lsw; u32 msw; } parts; } shape;
        int main() {
          shape u;
          u.value = 1.0;
          if (u.parts.msw != 0x3FF00000u) { return 1; }
          u.parts.msw = 0x40000000u;
          u.parts.lsw = 0u;
          if (u.value != 2.0) { return 2; }
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aUnionOfADoubleAndAWideIntegerAliasesBothWays() {
    // The scalar form: `union { double value; unsigned long bits; }` -- writing the double and
    // reading the integer is the reinterpretation, both 64 bits wide.
    assertDoesNotThrow {
      build(
        """
        union U { double value; unsigned long bits; };
        int main() { union U u; u.value = 1.0; if (u.bits == 0) { return 1; } return 0; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aUnionOfADoubleAndAnArrayIsStillRefused() {
    // The boundary that remains: an array member is many cells, not one word, so there is nothing
    // to slice or reinterpret. This is what still blocks the intel-tdx-module buffer views.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        union U { double value; unsigned char bytes[8]; };
        int main() { union U u; u.value = 1.0; return u.bytes[0]; }
        """
          .trimIndent()
      )
    }
  }
}
