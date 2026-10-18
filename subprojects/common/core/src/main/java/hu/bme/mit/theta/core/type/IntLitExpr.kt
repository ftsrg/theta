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

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import java.math.BigInteger

class IntLitExpr private constructor(val value: BigInteger) :
  NullaryExpr<IntType>(), LitExpr<IntType>, Comparable<IntLitExpr> {

  @Volatile private var hashCode = 0

  override val type: IntType
    get() = Int()

  override fun eval(valuation: Valuation): IntLitExpr = this

  fun toRat(): RatLitExpr = Rat(value, 1)

  fun add(that: IntLitExpr): IntLitExpr = of(value.add(that.value))

  fun sub(that: IntLitExpr): IntLitExpr = of(value.subtract(that.value))

  fun neg(): IntLitExpr = of(value.negate())

  fun pos(): IntLitExpr = of(value)

  fun div(that: IntLitExpr): IntLitExpr {
    // Semantics:
    // 5 div 3 = 1
    // 5 div -3 = -1
    // -5 div 3 = -2
    // -5 div -3 = 2
    var result = value.divide(that.value)
    if (value.signum() < 0 && value.mod(that.value.abs()).signum() != 0) {
      result = result.subtract(BigInteger.valueOf(that.value.signum().toLong()))
    }
    return of(result)
  }

  fun mod(that: IntLitExpr): IntLitExpr {
    // Always positive semantics:
    // 5 mod 3 = 2
    // 5 mod -3 = 2
    // -5 mod 3 = 1
    // -5 mod -3 = 1
    var result = value.mod(that.value.abs())
    if (result.signum() < 0) {
      result = result.add(that.value.abs())
    }
    assert(result.signum() >= 0)
    return of(result)
  }

  fun rem(that: IntLitExpr): IntLitExpr {
    // Semantics:
    // 5 rem 3 = 2
    // 5 rem -3 = -2
    // -5 rem 3 = 1
    // -5 rem -3 = -1
    val thisAbs = value.abs()
    val thatAbs = that.value.abs()
    return if (value.signum() < 0 && that.value.signum() < 0) {
      var result = thisAbs.mod(thatAbs)
      if (result.signum() != 0) {
        result = result.subtract(thatAbs)
      }
      of(result)
    } else if (value.signum() >= 0 && that.value.signum() < 0) {
      of(thisAbs.mod(thatAbs).negate())
    } else if (value.signum() < 0 && that.value.signum() >= 0) {
      var result = thisAbs.mod(thatAbs)
      if (result.signum() != 0) {
        result = thatAbs.subtract(result)
      }
      of(result)
    } else {
      of(value.mod(that.value))
    }
  }

  fun eq(that: IntLitExpr): BoolLitExpr = Bool(value.compareTo(that.value) == 0)

  fun neq(that: IntLitExpr): BoolLitExpr = Bool(value.compareTo(that.value) != 0)

  fun lt(that: IntLitExpr): BoolLitExpr = Bool(value < that.value)

  fun leq(that: IntLitExpr): BoolLitExpr = Bool(value <= that.value)

  fun gt(that: IntLitExpr): BoolLitExpr = Bool(value > that.value)

  fun geq(that: IntLitExpr): BoolLitExpr = Bool(value >= that.value)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + value.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null &&
        javaClass == other.javaClass &&
        value.compareTo((other as IntLitExpr).value) == 0)

  override fun toString(): String = value.toString()

  override fun compareTo(other: IntLitExpr): Int = value.compareTo(other.value)

  companion object {
    private const val HASH_SEED = 4111

    @JvmStatic fun of(value: BigInteger): IntLitExpr = IntLitExpr(value)
  }
}
