/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.core.type.rattype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.serialization.BigIntegerSerializer
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import java.math.BigInteger

@Serializable
@SerialName("RatLit")
data class RatLitExpr(
    @Serializable(with = BigIntegerSerializer::class)
    val num: BigInteger,
    @Serializable(with = BigIntegerSerializer::class)
    val denom: BigInteger
) : NullaryExpr<RatType>(), LitExpr<RatType>, Comparable<RatLitExpr> {

    init {
        require(denom != BigInteger.ZERO)
    }

    companion object {

        @JvmStatic
        fun of(num: BigInteger, denom: BigInteger): RatLitExpr {
            require(denom != BigInteger.ZERO) { "Denominator cannot be zero" }

            val gcd = num.abs().gcd(denom.abs())
            val (simplifiedNum, simplifiedDenom) = if (denom >= BigInteger.ZERO) {
                num.divide(gcd) to denom.divide(gcd)
            } else {
                num.divide(gcd).negate() to denom.divide(gcd).negate()
            }
            return RatLitExpr(simplifiedNum, simplifiedDenom)
        }
    }

    override val type: RatType = Rat()
    override fun eval(`val`: Valuation): RatLitExpr = this

    fun sign(): Int = num.signum()
    fun floor(): BigInteger =
        if (num >= BigInteger.ZERO || num.mod(denom) == BigInteger.ZERO) num / denom
        else num / denom - BigInteger.ONE

    fun ceil(): BigInteger =
        if (num <= BigInteger.ZERO || num.mod(denom) == BigInteger.ZERO) num / denom
        else num / denom + BigInteger.ONE

    fun add(that: RatLitExpr) =
        of(this.num * that.denom + this.denom * that.num, this.denom * that.denom)

    fun sub(that: RatLitExpr) =
        of(this.num * that.denom - this.denom * that.num, this.denom * that.denom)

    fun pos() = of(this.num, this.denom)
    fun neg() = of(this.num.negate(), this.denom)
    fun mul(that: RatLitExpr) =
        of(this.num * that.num, this.denom * that.denom)

    fun div(that: RatLitExpr) =
        of(this.num * that.denom, this.denom * that.num)

    fun eq(that: RatLitExpr) = Bool(this.num == that.num && this.denom == that.denom)
    fun neq(that: RatLitExpr) = Bool(this.num != that.num || this.denom != that.denom)
    fun lt(that: RatLitExpr) = Bool(this.num * that.denom < this.denom * that.num)
    fun leq(that: RatLitExpr) = Bool(this.num * that.denom <= this.denom * that.num)
    fun gt(that: RatLitExpr) = Bool(this.num * that.denom > this.denom * that.num)
    fun geq(that: RatLitExpr) = Bool(this.num * that.denom >= this.denom * that.num)
    fun abs(): RatLitExpr = of(num.abs(), denom)
    fun frac(): RatLitExpr = sub(of(floor(), BigInteger.ONE))

    override fun compareTo(other: RatLitExpr): Int =
        (this.num * other.denom).compareTo(this.denom * other.num)

    fun toInt(): IntLitExpr = IntLitExpr(num.divide(denom))

    override fun toString(): String = "$num%$denom"
}

