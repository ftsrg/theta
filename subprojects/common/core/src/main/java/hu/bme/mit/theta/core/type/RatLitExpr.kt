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
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import java.math.BigInteger

class RatLitExpr private constructor(num: BigInteger, denom: BigInteger) :
  NullaryExpr<RatType>(), LitExpr<RatType>, Comparable<RatLitExpr> {

  val num: BigInteger
  val denom: BigInteger

  @Volatile private var hashCode = 0

  init {
    checkArgument(denom.signum() != 0)
    val gcd = num.abs().gcd(denom.abs())
    if (denom.signum() >= 0) {
      this.num = num.divide(gcd)
      this.denom = denom.divide(gcd)
    } else {
      this.num = num.divide(gcd).negate()
      this.denom = denom.divide(gcd).negate()
    }
  }

  override val type: RatType
    get() = Rat()

  override fun eval(valuation: Valuation): LitExpr<RatType> = this

  fun sign(): Int = num.signum()

  fun floor(): BigInteger =
    if (num.signum() >= 0 || num.mod(denom).signum() == 0) num.divide(denom)
    else num.divide(denom).subtract(BigInteger.ONE)

  fun ceil(): BigInteger =
    if (num.signum() <= 0 || num.mod(denom).signum() == 0) num.divide(denom)
    else num.divide(denom).add(BigInteger.ONE)

  fun add(that: RatLitExpr): RatLitExpr =
    of(num.multiply(that.denom).add(denom.multiply(that.num)), denom.multiply(that.denom))

  fun sub(that: RatLitExpr): RatLitExpr =
    of(num.multiply(that.denom).subtract(denom.multiply(that.num)), denom.multiply(that.denom))

  fun pos(): RatLitExpr = of(num, denom)

  fun neg(): RatLitExpr = of(num.negate(), denom)

  fun mul(that: RatLitExpr): RatLitExpr = of(num.multiply(that.num), denom.multiply(that.denom))

  fun div(that: RatLitExpr): RatLitExpr = of(num.multiply(that.denom), denom.multiply(that.num))

  fun eq(that: RatLitExpr): BoolLitExpr =
    Bool(num.compareTo(that.num) == 0 && denom.compareTo(that.denom) == 0)

  fun neq(that: RatLitExpr): BoolLitExpr =
    Bool(num.compareTo(that.num) != 0 || denom.compareTo(that.denom) != 0)

  fun lt(that: RatLitExpr): BoolLitExpr = Bool(compareTo(that) < 0)

  fun leq(that: RatLitExpr): BoolLitExpr = Bool(compareTo(that) <= 0)

  fun gt(that: RatLitExpr): BoolLitExpr = Bool(compareTo(that) > 0)

  fun geq(that: RatLitExpr): BoolLitExpr = Bool(compareTo(that) >= 0)

  fun abs(): RatLitExpr = of(num.abs(), denom)

  fun frac(): RatLitExpr = sub(of(floor(), BigInteger.ONE))

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + num.hashCode()
      result = 31 * result + denom.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as RatLitExpr
    return num.compareTo(that.num) == 0 && denom.compareTo(that.denom) == 0
  }

  override fun toString(): String = "$num%$denom"

  override fun compareTo(other: RatLitExpr): Int =
    num.multiply(other.denom).compareTo(denom.multiply(other.num))

  fun toInt(): IntLitExpr = IntLitExpr.of(num.divide(denom))

  companion object {
    private const val HASH_SEED = 149

    @JvmStatic fun of(num: BigInteger, denom: BigInteger): RatLitExpr = RatLitExpr(num, denom)
  }
}
