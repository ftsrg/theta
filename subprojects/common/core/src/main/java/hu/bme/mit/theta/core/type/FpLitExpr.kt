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
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.FpUtils.bigFloatToFpLitExpr
import hu.bme.mit.theta.core.utils.FpUtils.fpLitExprToBigFloat
import hu.bme.mit.theta.core.utils.FpUtils.getMathContext
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import org.kframework.mpfr.BigFloat
import org.kframework.mpfr.BinaryMathContext

@Serializable
class FpLitExpr
private constructor(val hidden: Boolean, val exponent: BvLitExpr, val significand: BvLitExpr) :
  NullaryExpr<FpType>(), LitExpr<FpType>, Comparable<FpType> {

  @Transient @Volatile private var hashCode = 0

  fun isNaN(): Boolean = exponent.value.all { it } && significand.value.any { it }

  fun isPositiveInfinity(): Boolean =
    !hidden && exponent.value.all { it } && significand.value.none { it }

  fun isNegativeInfinity(): Boolean =
    hidden && exponent.value.all { it } && significand.value.none { it }

  fun isNegativeZero(): Boolean =
    !hidden && exponent.value.none { it } && significand.value.none { it }

  fun isPositiveZero(): Boolean =
    hidden && exponent.value.none { it } && significand.value.none { it }

  private inline fun arith(
    roundingMode: FpRoundingMode?,
    that: FpLitExpr,
    op: BigFloat.(BigFloat, BinaryMathContext) -> BigFloat,
  ): FpLitExpr {
    checkArgument(type == that.type)
    val result =
      fpLitExprToBigFloat(roundingMode, this)
        .op(fpLitExprToBigFloat(roundingMode, that), getMathContext(type, roundingMode))
    return bigFloatToFpLitExpr(result, type)
  }

  fun add(roundingMode: FpRoundingMode?, that: FpLitExpr): FpLitExpr =
    arith(roundingMode, that) { other, ctx -> add(other, ctx) }

  fun sub(roundingMode: FpRoundingMode?, that: FpLitExpr): FpLitExpr =
    arith(roundingMode, that) { other, ctx -> subtract(other, ctx) }

  fun pos(): FpLitExpr = this

  fun neg(): FpLitExpr {
    val neg = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this).negate()
    return bigFloatToFpLitExpr(neg, type)
  }

  fun mul(roundingMode: FpRoundingMode?, that: FpLitExpr): FpLitExpr =
    arith(roundingMode, that) { other, ctx -> multiply(other, ctx) }

  fun div(roundingMode: FpRoundingMode?, that: FpLitExpr): FpLitExpr =
    arith(roundingMode, that) { other, ctx -> divide(other, ctx) }

  private fun sameBits(that: FpLitExpr): Boolean =
    hidden == that.hidden && exponent == that.exponent && significand == that.significand

  /** Compares as IEEE floats: NaN compares false with everything. */
  private inline fun compare(that: FpLitExpr, cmp: (BigFloat, BigFloat) -> Boolean): BoolLitExpr {
    checkArgument(type == that.type)
    val left = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this)
    val right = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), that)
    if (left.isNaN || right.isNaN) {
      return BoolExprs.False()
    }
    return BoolExprs.Bool(cmp(left, right))
  }

  fun eq(that: FpLitExpr): BoolLitExpr = compare(that) { _, _ -> sameBits(that) }

  fun assign(that: FpLitExpr): BoolLitExpr {
    checkArgument(type == that.type)
    return BoolExprs.Bool(sameBits(that))
  }

  fun gt(that: FpLitExpr): BoolLitExpr = compare(that) { l, r -> l.greaterThan(r) }

  fun lt(that: FpLitExpr): BoolLitExpr = compare(that) { l, r -> l.lessThan(r) }

  fun geq(that: FpLitExpr): BoolLitExpr = compare(that) { l, r -> l.greaterThanOrEqualTo(r) }

  fun leq(that: FpLitExpr): BoolLitExpr = compare(that) { l, r -> l.lessThanOrEqualTo(r) }

  fun neq(that: FpLitExpr): BoolLitExpr = compare(that) { _, _ -> !sameBits(that) }

  override val type: FpType
    get() = FpType.of(exponent.type.size, significand.type.size + 1)

  override fun eval(valuation: Valuation): LitExpr<FpType> = this

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + hidden.hashCode()
      result = 31 * result + exponent.hashCode()
      result = 31 * result + significand.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    if (other is TraceableWrapperExpr<*>) equals(other.expr)
    else
      other != null &&
        javaClass == other.javaClass &&
        type == (other as FpLitExpr).type &&
        exponent == other.exponent &&
        hidden == other.hidden &&
        significand == other.significand

  override fun toString(): String =
    Utils.lispStringBuilder(if (hidden) "#b1" else "#b0")
      .add(exponent.toString())
      .add(significand.toString())
      .toString()

  override fun compareTo(other: FpType): Int = 0

  companion object {
    private const val HASH_SEED = 4254

    @JvmStatic
    fun of(hidden: Boolean, exponent: BvLitExpr, significand: BvLitExpr): FpLitExpr =
      FpLitExpr(hidden, exponent, significand)

    @JvmStatic
    fun of(value: BvLitExpr, fpType: FpType): FpLitExpr {
      val literal = value.value
      checkArgument(fpType.exponent + fpType.significand + 1 == literal.size)
      return FpLitExpr(
        literal[0],
        BvLitExpr.of(literal.copyOfRange(1, fpType.exponent + 1)),
        BvLitExpr.of(
          literal.copyOfRange(fpType.exponent + 1, fpType.exponent + fpType.significand + 1)
        ),
      )
    }

    @JvmStatic
    fun of(hidden: BvLitExpr, exponent: BvLitExpr, significand: BvLitExpr): FpLitExpr =
      FpLitExpr(hidden.value[0], exponent, significand)
  }
}
