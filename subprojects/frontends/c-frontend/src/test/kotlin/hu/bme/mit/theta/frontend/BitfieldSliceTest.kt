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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.BitfieldSlice
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

/**
 * The bit-slice read/write that packed bitfields lower to, checked by constant-folding on concrete
 * cells in both arithmetic encodings. Layout under test: a single byte holding b:2=2, c:2=3,
 * d:4=4, i.e. 4<<4 | 3<<2 | 2 = 78.
 */
class BitfieldSliceTest {

  private fun intCell(v: Long): Expr<IntType> = IntExprs.Int(BigInteger.valueOf(v))

  private fun bvCell(v: Long, size: Int): Expr<BvType> =
    BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(v), size)

  private fun fold(e: Expr<*>): BigInteger =
    when (val s = ExprUtils.simplify(e as Expr<Type>)) {
      is IntLitExpr -> s.value
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(s)
      else -> error("did not fold to a literal: $s")
    }

  @Test
  fun readUnsignedInt() {
    assertEquals(BigInteger.valueOf(2), fold(BitfieldSlice.read(intCell(78), 0, 2, false)))
    assertEquals(BigInteger.valueOf(3), fold(BitfieldSlice.read(intCell(78), 2, 2, false)))
    assertEquals(BigInteger.valueOf(4), fold(BitfieldSlice.read(intCell(78), 4, 4, false)))
  }

  @Test
  fun readUnsignedBv() {
    assertEquals(BigInteger.valueOf(2), fold(BitfieldSlice.read(bvCell(78, 8), 0, 2, false)))
    assertEquals(BigInteger.valueOf(3), fold(BitfieldSlice.read(bvCell(78, 8), 2, 2, false)))
    assertEquals(BigInteger.valueOf(4), fold(BitfieldSlice.read(bvCell(78, 8), 4, 4, false)))
  }

  @Test
  fun writeThenReadRoundTripsInt() {
    // Build 78 field by field, then read each back independently (no cross-field clobber).
    var cell: Expr<IntType> = intCell(0)
    cell = BitfieldSlice.write(cell, intCell(2), 0, 2) as Expr<IntType>
    cell = BitfieldSlice.write(cell, intCell(3), 2, 2) as Expr<IntType>
    cell = BitfieldSlice.write(cell, intCell(4), 4, 4) as Expr<IntType>
    assertEquals(BigInteger.valueOf(78), fold(cell))
    assertEquals(BigInteger.valueOf(2), fold(BitfieldSlice.read(cell, 0, 2, false)))
    assertEquals(BigInteger.valueOf(3), fold(BitfieldSlice.read(cell, 2, 2, false)))
    assertEquals(BigInteger.valueOf(4), fold(BitfieldSlice.read(cell, 4, 4, false)))
  }

  @Test
  fun writeThenReadRoundTripsBv() {
    var cell: Expr<BvType> = bvCell(0, 8)
    cell = BitfieldSlice.write(cell, bvCell(2, 8), 0, 2) as Expr<BvType>
    cell = BitfieldSlice.write(cell, bvCell(3, 8), 2, 2) as Expr<BvType>
    cell = BitfieldSlice.write(cell, bvCell(4, 8), 4, 4) as Expr<BvType>
    assertEquals(BigInteger.valueOf(78), fold(cell))
    assertEquals(BigInteger.valueOf(2), fold(BitfieldSlice.read(cell, 0, 2, false)))
    assertEquals(BigInteger.valueOf(3), fold(BitfieldSlice.read(cell, 2, 2, false)))
    assertEquals(BigInteger.valueOf(4), fold(BitfieldSlice.read(cell, 4, 4, false)))
  }

  @Test
  fun writingOneFieldDoesNotDisturbAnother() {
    // The soundness property packing must preserve: overwriting c leaves b and d intact.
    var cell: Expr<IntType> = intCell(78) // b=2, c=3, d=4
    cell = BitfieldSlice.write(cell, intCell(1), 2, 2) as Expr<IntType> // c := 1
    assertEquals(BigInteger.valueOf(2), fold(BitfieldSlice.read(cell, 0, 2, false)), "b intact")
    assertEquals(BigInteger.valueOf(1), fold(BitfieldSlice.read(cell, 2, 2, false)), "c updated")
    assertEquals(BigInteger.valueOf(4), fold(BitfieldSlice.read(cell, 4, 4, false)), "d intact")
  }

  /** A bitvector cell folds to a bit pattern; read it back the way its width says signed values. */
  private fun foldSigned(e: Expr<*>, bits: Int): BigInteger {
    val raw = fold(e)
    val half = BigInteger.ONE.shiftLeft(bits - 1)
    return if (raw >= half) raw.subtract(BigInteger.ONE.shiftLeft(bits)) else raw
  }

  @Test
  fun signedFieldSignExtends() {
    // A 2-bit signed field holding 0b11 is -1, not 3; 0b01 is 1. The integer encoding yields -1
    // directly (Int is unbounded); the bitvector encoding yields the sign-extended pattern 0xFF,
    // which is -1 read as an 8-bit signed value.
    assertEquals(BigInteger.valueOf(-1), fold(BitfieldSlice.read(intCell(0b11), 0, 2, true)))
    assertEquals(BigInteger.valueOf(1), fold(BitfieldSlice.read(intCell(0b01), 0, 2, true)))
    assertEquals(
      BigInteger.valueOf(-1),
      foldSigned(BitfieldSlice.read(bvCell(0b11, 8), 0, 2, true), 8),
    )
    assertEquals(
      BigInteger.valueOf(1),
      foldSigned(BitfieldSlice.read(bvCell(0b01, 8), 0, 2, true), 8),
    )
  }
}
