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
  fun anArrayMemberIsNowByteAddressed() {
    // AD7, the intractable half. `union { uint64_t raw; uint8_t bytes[8]; }` has no single word a
    // narrower member could slice out of -- an array is many cells, not one -- so this used to be
    // refused outright ("members do not all share a representation"), which is what blocked the
    // intel-tdx-module cluster (596 ERRORs on exactly this shape). Byte-granular cells fix that:
    // `u.bytes[i]` is just the byte at offset `i`, plain address arithmetic under both encodings.
    for (arithmetic in listOf(ArithmeticType.efficient, ArithmeticType.bitvector)) {
      assertDoesNotThrow({
        build(
          """
          union U { unsigned long raw; unsigned char bytes[8]; };
          int main() { union U u; u.raw = 0; return u.bytes[0]; }
          """
            .trimIndent(),
          arithmetic,
        )
      }, "byte array member of a byte-laid-out union under $arithmetic")
    }
  }

  @Test
  fun uint128StyleUnionByteAddressesQwordsDwordsAndBytesTogether() {
    // The motivating intel-tdx-module shape: three views of the same 16 bytes, none of which is a
    // single word every sibling can share -- qwords[2]/dwords[4]/bytes[16] each need real byte
    // cells. Little-endian recombination (u.qwords[0] = 0x0102030405060708 => u.bytes[0] == 0x08,
    // u.bytes[7] == 0x01, u.dwords[0] == 0x05060708) is checked end to end by the actual analysis
    // under both encodings -- it proves Safe, and negating the assertion proves Unsafe, so the
    // check is not vacuous -- the same pattern union_slice_punning.c documents for batch 56. This
    // frontend-level test only pins that the shape keeps reaching the frontend at all.
    for (arithmetic in listOf(ArithmeticType.efficient, ArithmeticType.bitvector)) {
      assertDoesNotThrow({
        build(
          """
          typedef union {
            unsigned long qwords[2];
            unsigned int dwords[4];
            unsigned char bytes[16];
          } uint128_t;
          int main() {
            uint128_t u;
            u.qwords[0] = 0x0102030405060708UL;
            u.qwords[1] = 0;
            return u.bytes[0] + u.dwords[0];
          }
          """
            .trimIndent(),
          arithmetic,
        )
      }, "uint128_t-style byte-addressed union under $arithmetic")
    }
  }

  @Test
  fun byteAddressedUnionSupportsAVariableIndex() {
    // The whole point of byte cells over a bit-sliced word: `u.bytes[i]` is bytes [i, i+1), an
    // *arithmetic* offset, so a nondeterministic in-range `i` is just as fine as a literal one --
    // unlike a variable bit-shift, which is only expressible under bitvector.
    for (arithmetic in listOf(ArithmeticType.efficient, ArithmeticType.bitvector)) {
      assertDoesNotThrow({
        build(
          """
          extern int __VERIFIER_nondet_int(void);
          union U { unsigned long raw; unsigned char bytes[8]; };
          int main() {
            union U u;
            u.raw = 0x0102030405060708UL;
            int i = __VERIFIER_nondet_int();
            if (i < 0 || i >= 8) { return 0; }
            return u.bytes[i];
          }
          """
            .trimIndent(),
          arithmetic,
        )
      }, "variable-index byte access under $arithmetic")
    }
  }

  @Test
  fun addressOfASingleByteCellIsFine() {
    // `&u.bytes[i]` names exactly one byte cell, so the resulting pointer is perfectly meaningful
    // and must not be refused.
    assertDoesNotThrow {
      build(
        """
        union U { unsigned long qwords[2]; unsigned char bytes[16]; };
        int main() {
          union U u;
          u.qwords[0] = 0;
          unsigned char *p = &u.bytes[0];
          return *p;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun addressOfAMultiByteMemberIsRefused() {
    // `&u.qwords[0]` would need a pointer that knows it reads 8 byte-cells as one value -- nothing
    // in this model can express that, so it is refused rather than guessed at.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        union U { unsigned long qwords[2]; unsigned char bytes[16]; };
        int main() {
          union U u;
          u.qwords[0] = 0;
          unsigned long *p = &u.qwords[0];
          return (int) *p;
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aBitfieldInsideAByteLaidOutUnionIsStillRefused() {
    // A bitfield is not a whole number of bytes, so it has no place in the byte-cell model; the
    // union still needs byte cells for `bytes`, so this must stay refused rather than guessed at.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        union U { unsigned char bytes[8]; unsigned int lo:4; };
        int main() { union U u; u.bytes[0] = 0; return (int) u.lo; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aNestedAggregateInsideAByteLaidOutUnionIsStillRefused() {
    // A nested struct member would need its own base id (the containment model), which this core
    // implementation does not wire up; refused rather than guessed at.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        union U {
          unsigned char bytes[8];
          struct { unsigned long lo; unsigned long hi; } parts;
        };
        int main() { union U u; u.bytes[0] = 0; return (int) u.parts.lo; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aFloatingPointMemberInsideAByteLaidOutUnionIsStillRefused() {
    // The batch-59 NaN gate on fpToIEEEBV applies here too, not just to the word-sliceable path --
    // the union still needs byte cells for `bytes`, so this must stay refused rather than reopen
    // the unsound round-trip.
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        union U { unsigned char bytes[8]; double d; };
        int main() { union U u; u.bytes[0] = 0; return (int) u.d; }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun aFloatingPointMemberIsRefusedWhileTheNanRoundTripIsUnsound() {
    // The FpToIeeeBv / FpFromIeeeBv machinery for float union punning exists and is correct on
    // finite values, but is GATED OFF: fpToIEEEBV is unspecified for NaN, and a NaN routed through
    // the integer view and back (`value = NaN; word = ...; value = word`, the newlib idiom) still
    // yields a spurious non-NaN in the solver -- 14 wrong float-newlib results in the 2026-07-21
    // run. Until the round-trip is sound the float union is refused, which scores 0 rather than a
    // wrong answer's -16. (See PLAN.md batch 59.)
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        typedef unsigned int u32;
        typedef union { float value; u32 word; } shape;
        int main() { shape u; u.value = 1.0f; return u.word; }
        """
          .trimIndent()
      )
    }
  }
}
