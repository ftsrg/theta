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
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Struct
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

/**
 * A power-of-2-sized `_Atomic` object aligns to its own size, even where the architecture would cap
 * a plain scalar lower — the i386 quirk that `long long`/`double` align to 4, which `_Atomic`
 * bypasses so the object can be read or written with a single atomic instruction (Oracle E60778,
 * https://docs.oracle.com/cd/E60778_01/html/E60745/gqfbq.html). Every expectation here is gcc's:
 * `gcc -m32`/`-m64` on the same struct, printing `sizeof`/`_Alignof`/`offsetof`.
 */
class AtomicAlignmentTest {

  private fun layoutOf(src: String, tag: String, arch: ArchitectureType): ObjectLayout.Layout {
    val parseContext = ParseContext()
    parseContext.architecture = arch
    getXcfaFromC(
      src.byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
    val struct = requireNotNull(Struct.getByName(tag, false)) { "struct $tag was not registered" }
    return ObjectLayout.of(struct.actualType as CStruct, arch)
  }

  private fun bothModels(block: (ArchitectureType) -> Unit) {
    listOf(ArchitectureType.ILP32, ArchitectureType.LP64).forEach(block)
  }

  @Test
  fun atomicLongLongMemberAlignsToItsSizeUnderIlp32() {
    // gcc -m32: struct AtLL { _Atomic long long a; char c; } -> size 16, align 8, c at byte 8.
    val atomic =
      layoutOf(
        "struct AtLL { _Atomic long long a; char c; }; struct AtLL g; int main(){ return g.c; }",
        "AtLL",
        ArchitectureType.ILP32,
      )
    assertEquals(64, atomic.bitAlignment, "_Atomic long long forces 8-byte struct alignment on i386")
    assertEquals(128, atomic.bitSize, "and rounds the size up to 16 bytes")
    assertEquals(64, atomic.field("c")!!.bitOffset, "c sits after the 8-byte atomic member")
  }

  @Test
  fun plainLongLongStaysCappedUnderIlp32() {
    // The control: gcc -m32: struct PlLL { long long a; char c; } -> size 12, align 4, c at byte 8.
    val plain =
      layoutOf(
        "struct PlLL { long long a; char c; }; struct PlLL g; int main(){ return g.c; }",
        "PlLL",
        ArchitectureType.ILP32,
      )
    assertEquals(32, plain.bitAlignment, "plain long long caps at 4-byte alignment on i386")
    assertEquals(96, plain.bitSize, "size 12 bytes")
  }

  @Test
  fun atomicLongLongUnchangedUnderLp64() {
    // LP64 already aligns long long to 8, so _Atomic changes nothing: size 16, align 8.
    val l =
      layoutOf(
        "struct AtLL2 { _Atomic long long a; char c; }; struct AtLL2 g; int main(){ return g.c; }",
        "AtLL2",
        ArchitectureType.LP64,
      )
    assertEquals(64, l.bitAlignment)
    assertEquals(128, l.bitSize)
  }

  @Test
  fun atomicIntKeepsNaturalAlignmentInBothModels() {
    // _Atomic int is 4/4 in both models -- already within the cap, so nothing changes: size 8.
    bothModels { arch ->
      val l =
        layoutOf(
          "struct AtI { _Atomic int a; char c; }; struct AtI g; int main(){ return g.c; }",
          "AtI",
          arch,
        )
      assertEquals(32, l.bitAlignment, "_Atomic int stays 4-byte aligned, $arch")
      assertEquals(64, l.bitSize, "$arch")
    }
  }
}
