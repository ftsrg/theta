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
package hu.bme.mit.theta.core.type

import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToNeutralBvLitExpr
import hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToSignedBvLitExpr
import hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToUnsignedBvLitExpr
import hu.bme.mit.theta.core.utils.BvUtils.fitBigIntegerIntoNeutralDomain
import hu.bme.mit.theta.core.utils.BvUtils.fitBigIntegerIntoSignedDomain
import hu.bme.mit.theta.core.utils.BvUtils.fitBigIntegerIntoUnsignedDomain
import hu.bme.mit.theta.core.utils.BvUtils.neutralBvLitExprToBigInteger
import hu.bme.mit.theta.core.utils.BvUtils.signedBvLitExprToBigInteger
import hu.bme.mit.theta.core.utils.BvUtils.unsignedBvLitExprToBigInteger
import java.math.BigInteger

class BvLitExpr private constructor(val value: BooleanArray, private val signed: Boolean?) :
  NullaryExpr<BvType>(), LitExpr<BvType>, Comparable<BvLitExpr> {

  @Volatile private var hashCode = 0

  init {
    checkArgument(value.isNotEmpty(), "Bitvector must have positive size")
  }

  override val type: BvType
    get() = BvType.of(value.size, signed)

  override fun eval(valuation: Valuation): LitExpr<BvType> = this

  /**
   * A literal of the same width as this one, keeping its signedness.
   *
   * Building the result "neutrally" instead -- as every one of these operations used to -- throws
   * the signedness away, and a bitvector without one cannot be compared at all ([BvType.Lt] and
   * friends reject it). It only ever showed up once a value was *constant-folded*: the expression
   * tree carries proper types, but as soon as an operation over two literals was evaluated, the
   * result was neutral, and any later comparison against it failed.
   */
  private fun sameSignedness(bits: BooleanArray): BvLitExpr = Bv(bits, type.signedness)

  private fun sameSignedness(value: BigInteger): BvLitExpr =
    sameSignedness(bigIntegerToNeutralBvLitExpr(value, type.size).value)

  private fun checkSameType(that: BvLitExpr) = checkArgument(type == that.type)

  fun concat(that: BvLitExpr): BvLitExpr {
    val concated = BooleanArray(type.size + that.type.size)
    for (i in 0 until type.size) concated[i] = value[i]
    for (i in 0 until that.type.size) concated[type.size + i] = that.value[i]
    return sameSignedness(concated)
  }

  fun extract(from: IntLitExpr, until: IntLitExpr): BvLitExpr {
    val fromValue = from.value.toInt()
    val untilValue = until.value.toInt()
    checkArgument(fromValue >= 0)
    checkArgument(untilValue >= 0)
    checkArgument(untilValue > fromValue)
    val extracted = BooleanArray(untilValue - fromValue)
    for (i in extracted.indices) {
      extracted[extracted.size - i - 1] = value[value.size - (fromValue + i) - 1]
    }
    return sameSignedness(extracted)
  }

  fun zext(extendType: BvType): BvLitExpr = extend(extendType, false)

  fun sext(extendType: BvType): BvLitExpr = extend(extendType, value[0])

  private fun extend(extendType: BvType, fill: Boolean): BvLitExpr {
    checkArgument(extendType.size >= type.size)
    val extended = BooleanArray(extendType.size)
    for (i in value.indices) extended[extended.size - i - 1] = value[value.size - i - 1]
    for (i in 0 until extendType.size - type.size) extended[i] = fill
    return Bv(extended, extendType.signedness)
  }

  fun add(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    val sum = neutralBvLitExprToBigInteger(this).add(neutralBvLitExprToBigInteger(that))
    return sameSignedness(fitBigIntegerIntoNeutralDomain(sum, type.size))
  }

  fun sub(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    val sub = neutralBvLitExprToBigInteger(this).subtract(neutralBvLitExprToBigInteger(that))
    return sameSignedness(fitBigIntegerIntoNeutralDomain(sub, type.size))
  }

  fun mul(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    val prod = neutralBvLitExprToBigInteger(this).multiply(neutralBvLitExprToBigInteger(that))
    return sameSignedness(fitBigIntegerIntoNeutralDomain(prod, type.size))
  }

  fun pos(): BvLitExpr {
    val pos = fitBigIntegerIntoSignedDomain(signedBvLitExprToBigInteger(this), type.size)
    return bigIntegerToSignedBvLitExpr(pos, type.size)
  }

  fun neg(): BvLitExpr {
    val neg = fitBigIntegerIntoSignedDomain(signedBvLitExprToBigInteger(this).negate(), type.size)
    return bigIntegerToSignedBvLitExpr(neg, type.size)
  }

  fun udiv(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    if (unsignedBvLitExprToBigInteger(that).signum() == 0) {
      return sameSignedness(BigInteger.TWO.pow(type.size).subtract(BigInteger.ONE))
    }
    val div = unsignedBvLitExprToBigInteger(this).divide(unsignedBvLitExprToBigInteger(that))
    return bigIntegerToUnsignedBvLitExpr(fitBigIntegerIntoUnsignedDomain(div, type.size), type.size)
  }

  fun sdiv(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    if (signedBvLitExprToBigInteger(that).signum() == 0) {
      return sameSignedness(
        if (signedBvLitExprToBigInteger(this).signum() < 0) BigInteger.ONE
        else BigInteger.TWO.pow(type.size).subtract(BigInteger.ONE)
      )
    }
    val div = signedBvLitExprToBigInteger(this).divide(signedBvLitExprToBigInteger(that))
    return bigIntegerToSignedBvLitExpr(fitBigIntegerIntoSignedDomain(div, type.size), type.size)
  }

  fun and(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    return sameSignedness(
      neutralBvLitExprToBigInteger(this).and(neutralBvLitExprToBigInteger(that))
    )
  }

  fun or(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    return sameSignedness(neutralBvLitExprToBigInteger(this).or(neutralBvLitExprToBigInteger(that)))
  }

  fun xor(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    return sameSignedness(
      neutralBvLitExprToBigInteger(this).xor(neutralBvLitExprToBigInteger(that))
    )
  }

  fun not(): BvLitExpr = sameSignedness(neutralBvLitExprToBigInteger(this).not())

  /** Applies [step] to a copy of the bits once per unit of [that]'s value. */
  private inline fun shifted(that: BvLitExpr, step: (BooleanArray) -> Unit): BvLitExpr {
    checkSameType(that)
    val shifted = value.copyOf()
    val amount = neutralBvLitExprToBigInteger(that)
    var i = BigInteger.ZERO
    while (i < amount) {
      step(shifted)
      i = i.add(BigInteger.ONE)
    }
    return sameSignedness(shifted)
  }

  fun shiftLeft(that: BvLitExpr): BvLitExpr =
    shifted(that) { s ->
      for (j in 0 until s.size - 1) s[j] = s[j + 1]
      s[s.size - 1] = false
    }

  fun arithShiftRight(that: BvLitExpr): BvLitExpr {
    val insert = value[0]
    return shifted(that) { s ->
      for (j in s.size - 1 downTo 1) s[j] = s[j - 1]
      s[0] = insert
    }
  }

  fun logicShiftRight(that: BvLitExpr): BvLitExpr =
    shifted(that) { s ->
      for (j in s.size - 1 downTo 1) s[j] = s[j - 1]
      s[0] = false
    }

  fun rotateLeft(that: BvLitExpr): BvLitExpr =
    shifted(that) { s ->
      val rotated = s[0]
      for (j in 0 until s.size - 1) s[j] = s[j + 1]
      s[s.size - 1] = rotated
    }

  fun rotateRight(that: BvLitExpr): BvLitExpr =
    shifted(that) { s ->
      val rotated = s[s.size - 1]
      for (j in s.size - 1 downTo 1) s[j] = s[j - 1]
      s[0] = rotated
    }

  fun smod(that: BvLitExpr): BvLitExpr {
    checkSameType(that)
    // Semantics:
    // 5 mod 3 = 2
    // 5 mod -3 = -1
    // -5 mod 3 = 1
    // -5 mod -3 = -2
    // x mod 0 = x
    val divisor = signedBvLitExprToBigInteger(that)
    if (divisor.signum() == 0) {
      return this
    }
    var result = signedBvLitExprToBigInteger(this).mod(divisor.abs())
    if (divisor.signum() < 0 && result.signum() != 0) {
      result = result.add(divisor)
    }
    return bigIntegerToSignedBvLitExpr(result, type.size)
  }

  fun urem(that: BvLitExpr): BvLitExpr {
    // Semantics:
    // 5 rem 3 = 2
    val thisInt = unsignedBvLitExprToBigInteger(this)
    val thatInt = unsignedBvLitExprToBigInteger(that)
    if (thatInt.signum() == 0) {
      return this
    }
    return sameSignedness(thisInt.mod(thatInt))
  }

  fun srem(that: BvLitExpr): BvLitExpr {
    // Semantics:
    // 5 rem 3 = 2
    // 5 rem -3 = 2
    // -5 rem 3 = -1
    // -5 rem -3 = -1
    val thisInt = signedBvLitExprToBigInteger(this)
    val thatInt = signedBvLitExprToBigInteger(that)
    if (thatInt.signum() == 0) {
      return this
    }
    val thisAbs = thisInt.abs()
    val thatAbs = thatInt.abs()
    val result =
      if (thisInt.signum() < 0 && thatInt.signum() < 0) thisAbs.mod(thatAbs).negate()
      else if (thisInt.signum() >= 0 && thatInt.signum() < 0) thisAbs.mod(thatAbs)
      else if (thisInt.signum() < 0 && thatInt.signum() >= 0) thisAbs.mod(thatAbs).negate()
      else thisInt.mod(thatInt)
    return bigIntegerToSignedBvLitExpr(result, type.size)
  }

  fun eq(that: BvLitExpr): BoolLitExpr {
    checkSameType(that)
    return Bool(value.contentEquals(that.value))
  }

  fun neq(that: BvLitExpr): BoolLitExpr {
    checkSameType(that)
    return Bool(!value.contentEquals(that.value))
  }

  private fun unsignedCompare(that: BvLitExpr): Int {
    checkSameType(that)
    return unsignedBvLitExprToBigInteger(this).compareTo(unsignedBvLitExprToBigInteger(that))
  }

  private fun signedCompare(that: BvLitExpr): Int {
    checkSameType(that)
    return signedBvLitExprToBigInteger(this).compareTo(signedBvLitExprToBigInteger(that))
  }

  fun ult(that: BvLitExpr): BoolLitExpr = Bool(unsignedCompare(that) < 0)

  fun ule(that: BvLitExpr): BoolLitExpr = Bool(unsignedCompare(that) <= 0)

  fun ugt(that: BvLitExpr): BoolLitExpr = Bool(unsignedCompare(that) > 0)

  fun uge(that: BvLitExpr): BoolLitExpr = Bool(unsignedCompare(that) >= 0)

  fun slt(that: BvLitExpr): BoolLitExpr = Bool(signedCompare(that) < 0)

  fun sle(that: BvLitExpr): BoolLitExpr = Bool(signedCompare(that) <= 0)

  fun sgt(that: BvLitExpr): BoolLitExpr = Bool(signedCompare(that) > 0)

  fun sge(that: BvLitExpr): BoolLitExpr = Bool(signedCompare(that) >= 0)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + value.contentHashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null &&
        javaClass == other.javaClass &&
        value.contentEquals((other as BvLitExpr).value))

  override fun toString(): String = value.joinToString("", prefix = "#b") { if (it) "1" else "0" }

  override fun compareTo(other: BvLitExpr): Int {
    checkSameType(other)
    return neutralBvLitExprToBigInteger(this).compareTo(neutralBvLitExprToBigInteger(other))
  }

  companion object {
    private const val HASH_SEED = 5624

    @JvmStatic fun of(value: BooleanArray, signed: Boolean?): BvLitExpr = BvLitExpr(value, signed)

    @JvmStatic fun of(value: BooleanArray): BvLitExpr = of(value, null)
  }
}
