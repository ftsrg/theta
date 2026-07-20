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
package hu.bme.mit.theta.frontend

import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.BitfieldLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.BitfieldLayout.Member
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

/**
 * The pure storage-unit layout that packs consecutive bitfields into shared cells (PLAN.md batch
 * 43-design step 1). Not yet wired into member access; these pin the packing arithmetic in
 * isolation so the wiring can rely on it.
 */
class BitfieldLayoutTest {

  private fun ordinary(bits: Int) = Member(bits, -1)

  private fun bitfield(baseBits: Int, width: Int) = Member(baseBits, width)

  @Test
  fun ordinaryMembersEachTakeTheirOwnUnitLikeBefore() {
    // No bitfields: unit index == member position, byte-for-byte the historical layout.
    val layout = BitfieldLayout.compute(listOf(ordinary(32), ordinary(32), ordinary(8)))
    assertEquals(3, layout.unitCount)
    assertEquals(listOf(0, 1, 2), layout.slots.map { it.unitIndex })
    assertEquals(listOf(false, false, false), layout.slots.map { it.bitfield })
  }

  @Test
  fun packedBitfieldsShareAUnit() {
    // struct A { unsigned char a; unsigned char b:2; unsigned char c:2; unsigned char d:4; }
    // a -> unit 0; b,c,d pack into unit 1 (2+2+4 = 8 <= 8). 2 cells total, matching malloc(2).
    val layout =
      BitfieldLayout.compute(
        listOf(ordinary(8), bitfield(8, 2), bitfield(8, 2), bitfield(8, 4))
      )
    assertEquals(2, layout.unitCount, "the packed struct must occupy 2 cells, not 4")
    assertEquals(listOf(0, 1, 1, 1), layout.slots.map { it.unitIndex })
    assertEquals(listOf(0, 0, 2, 4), layout.slots.map { it.bitOffset })
    assertEquals(listOf(8, 2, 2, 4), layout.slots.map { it.width })
    assertEquals(listOf(false, true, true, true), layout.slots.map { it.bitfield })
  }

  @Test
  fun aBitfieldThatOverflowsTheUnitStartsANewOne() {
    // Three 6-bit fields in a 8-bit base: 6 fits, 6+6 > 8 -> new unit, 6+6 > 8 -> new unit.
    val layout =
      BitfieldLayout.compute(listOf(bitfield(8, 6), bitfield(8, 6), bitfield(8, 6)))
    assertEquals(3, layout.unitCount)
    assertEquals(listOf(0, 1, 2), layout.slots.map { it.unitIndex })
    assertEquals(listOf(0, 0, 0), layout.slots.map { it.bitOffset })
  }

  @Test
  fun anOrdinaryMemberBreaksABitfieldRun() {
    // b:4 -> unit 0; then ordinary -> unit 1; then c:4 must NOT rejoin unit 0 -> unit 2.
    val layout =
      BitfieldLayout.compute(listOf(bitfield(8, 4), ordinary(32), bitfield(8, 4)))
    assertEquals(3, layout.unitCount)
    assertEquals(listOf(0, 1, 2), layout.slots.map { it.unitIndex })
  }

  @Test
  fun namedZeroWidthBitfieldIsABoundaryWithNoStorage() {
    // a:4, then a 0-width boundary, then b:4 -> b starts a new unit; the boundary has no slot.
    val layout =
      BitfieldLayout.compute(listOf(bitfield(8, 4), bitfield(8, 0), bitfield(8, 4)))
    assertEquals(2, layout.slots.size, "the zero-width boundary produces no slot")
    assertEquals(2, layout.unitCount)
    assertEquals(listOf(0, 1), layout.slots.map { it.unitIndex })
  }

  @Test
  fun mixedRunsAcrossDifferentBaseWidths() {
    // int:20 (base 32) then int:20: 20 fits, 20+20 > 32 -> new unit.
    val layout = BitfieldLayout.compute(listOf(bitfield(32, 20), bitfield(32, 20)))
    assertEquals(2, layout.unitCount)
    assertEquals(listOf(0, 1), layout.slots.map { it.unitIndex })
  }
}
