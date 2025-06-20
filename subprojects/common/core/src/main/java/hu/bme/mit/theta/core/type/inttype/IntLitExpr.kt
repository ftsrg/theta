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

package hu.bme.mit.theta.core.type.inttype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.serialization.BigIntegerSerializer
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatLitExpr
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import java.math.BigInteger

@Serializable
@SerialName("IntLit")
data class IntLitExpr(
    @Serializable(with = BigIntegerSerializer::class)
    val value: BigInteger
) : NullaryExpr<IntType>(), LitExpr<IntType>, Comparable<IntLitExpr> {

    companion object {

        @JvmStatic
        fun of(value: BigInteger) = IntLitExpr(value)
    }

    override val type: IntType = Int()
    override fun eval(`val`: Valuation): IntLitExpr = this
    fun toRat(): RatLitExpr = Rat(this.value, 1)
    fun add(that: IntLitExpr) = IntLitExpr(this.value.add(that.value))
    fun sub(that: IntLitExpr) = IntLitExpr(this.value.subtract(that.value))
    fun neg() = IntLitExpr(this.value.negate())
    fun pos() = IntLitExpr(this.value)

    fun div(that: IntLitExpr): IntLitExpr {
        // Semantics:
        // 5 div 3 = 1
        // 5 div -3 = -1
        // -5 div 3 = -2
        // -5 div -3 = 2
        var result = this.value.divide(that.value)
        if (this.value < BigInteger.ZERO && this.value.mod(that.value.abs()) != BigInteger.ZERO) {
            result = result.subtract(BigInteger.valueOf(that.value.signum().toLong()))
        }
        return IntLitExpr(result)
    }

    fun mod(that: IntLitExpr): IntLitExpr {
        // Always positive semantics:
        // 5 mod 3 = 2
        // 5 mod -3 = 2
        // -5 mod 3 = 1
        // -5 mod -3 = 1
        var result = this.value.mod(that.value.abs())
        if (result < BigInteger.ZERO) {
            result = result.add(that.value.abs())
        }
        require(result >= BigInteger.ZERO)
        return IntLitExpr(result)
    }

    fun rem(that: IntLitExpr): IntLitExpr {
        // Semantics:
        // 5 rem 3 = 2
        // 5 rem -3 = -2
        // -5 rem 3 = 1
        // -5 rem -3 = -1
        val thisAbs = this.value.abs()
        val thatAbs = that.value.abs()
        return when {
            this.value < BigInteger.ZERO && that.value < BigInteger.ZERO -> {
                var result = thisAbs.mod(thatAbs)
                if (result != BigInteger.ZERO) result = result.subtract(thatAbs)
                IntLitExpr(result)
            }

            this.value >= BigInteger.ZERO && that.value < BigInteger.ZERO -> IntLitExpr(thisAbs.mod(thatAbs).negate())
            this.value < BigInteger.ZERO && that.value >= BigInteger.ZERO -> {
                var result = thisAbs.mod(thatAbs)
                if (result != BigInteger.ZERO) result = thatAbs.subtract(result)
                IntLitExpr(result)
            }

            else -> IntLitExpr(this.value.mod(that.value))
        }
    }

    fun eq(that: IntLitExpr) = Bool(this.value == that.value)
    fun neq(that: IntLitExpr) = Bool(this.value != that.value)
    fun lt(that: IntLitExpr) = Bool(this.value < that.value)
    fun leq(that: IntLitExpr) = Bool(this.value <= that.value)
    fun gt(that: IntLitExpr) = Bool(this.value > that.value)
    fun geq(that: IntLitExpr) = Bool(this.value >= that.value)
    override fun compareTo(other: IntLitExpr): Int = this.value.compareTo(other.value)
    override fun toString(): String = value.toString()
}

