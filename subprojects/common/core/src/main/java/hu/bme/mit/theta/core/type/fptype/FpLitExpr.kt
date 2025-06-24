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

package hu.bme.mit.theta.core.type.fptype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.utils.FpUtils.*
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import java.util.*

@Serializable
@SerialName("FpLit")
data class FpLitExpr(
    val hidden: Boolean,
    val exponent: BvLitExpr,
    val significand: BvLitExpr
) : NullaryExpr<FpType>(), LitExpr<FpType>, Comparable<FpType> {

    companion object {

        @JvmStatic
        fun of(hidden: Boolean, exponent: BvLitExpr, significand: BvLitExpr) =
            FpLitExpr(hidden, exponent, significand)

        @JvmStatic
        fun of(value: BvLitExpr, fpType: FpType): FpLitExpr {
            val literal = value.value
            require(fpType.exponent + fpType.significand + 1 == literal.size)
            return FpLitExpr(
                literal[0],
                BvLitExpr.of(Arrays.copyOfRange(literal, 1, fpType.exponent + 1)),
                BvLitExpr.of(
                    Arrays.copyOfRange(
                        literal,
                        fpType.exponent + 1,
                        fpType.exponent + fpType.significand + 1
                    )
                )
            )
        }

        @JvmStatic
        fun of(hidden: BvLitExpr, exponent: BvLitExpr, significand: BvLitExpr): FpLitExpr {
            val hiddenLit = hidden.value
            return FpLitExpr(hiddenLit[0], exponent, significand)
        }
    }

    override val type: FpType get() = FpType(exponent.type.size, significand.type.size)
    override fun eval(`val`: Valuation): FpLitExpr = this

    fun isNaN(): Boolean {
        var isNaN = true
        for (i in exponent.value) {
            isNaN = isNaN && i
        }
        var atLeastOne = false
        for (i in significand.value) {
            atLeastOne = atLeastOne || i
        }
        return isNaN && atLeastOne
    }

    fun isPositiveInfinity(): Boolean {
        var isNaN = !hidden
        for (i in exponent.value) {
            isNaN = isNaN && i
        }
        for (i in significand.value) {
            isNaN = isNaN && !i
        }
        return isNaN
    }

    fun isNegativeInfinity(): Boolean {
        var isNaN = hidden
        for (i in exponent.value) {
            isNaN = isNaN && i
        }
        for (i in significand.value) {
            isNaN = isNaN && !i
        }
        return isNaN
    }

    fun isNegativeZero(): Boolean {
        var isNaN = !hidden
        for (i in exponent.value) {
            isNaN = isNaN && !i
        }
        for (i in significand.value) {
            isNaN = isNaN && !i
        }
        return isNaN
    }

    fun isPositiveZero(): Boolean {
        var isNaN = hidden
        for (i in exponent.value) {
            isNaN = isNaN && !i
        }
        for (i in significand.value) {
            isNaN = isNaN && !i
        }
        return isNaN
    }

    fun add(roundingMode: FpRoundingMode, that: FpLitExpr): FpLitExpr {
        require(this.type == that.type)
        val sum =
            fpLitExprToBigFloat(roundingMode, this)
                .add(
                    fpLitExprToBigFloat(roundingMode, that),
                    getMathContext(this.type, roundingMode)
                )
        return bigFloatToFpLitExpr(sum, type)
    }

    fun sub(roundingMode: FpRoundingMode, that: FpLitExpr): FpLitExpr {
        require(this.type == that.type)
        val sub =
            fpLitExprToBigFloat(roundingMode, this)
                .subtract(
                    fpLitExprToBigFloat(roundingMode, that),
                    getMathContext(this.type, roundingMode)
                )
        return bigFloatToFpLitExpr(sub, type)
    }

    fun pos(): FpLitExpr = this

    fun neg(): FpLitExpr {
        val neg = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, this).negate()
        return bigFloatToFpLitExpr(neg, type)
    }

    fun mul(roundingMode: FpRoundingMode, that: FpLitExpr): FpLitExpr {
        require(this.type == that.type)
        val sub =
            fpLitExprToBigFloat(roundingMode, this)
                .multiply(
                    fpLitExprToBigFloat(roundingMode, that),
                    getMathContext(this.type, roundingMode)
                )
        return bigFloatToFpLitExpr(sub, type)
    }

    fun div(roundingMode: FpRoundingMode, that: FpLitExpr): FpLitExpr {
        require(this.type == that.type)
        val sub =
            fpLitExprToBigFloat(roundingMode, this)
                .divide(
                    fpLitExprToBigFloat(roundingMode, that),
                    getMathContext(this.type, roundingMode)
                )
        return bigFloatToFpLitExpr(sub, type)
    }

    fun eq(that: FpLitExpr): BoolLitExpr {
        require(this.type == that.type)
        val left = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, this)
        val right = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, that)
        if (left.isNaN || right.isNaN) {
            return False()
        }
        return Bool(this.hidden == that.hidden && exponent == that.exponent && significand == that.significand)
    }

    fun assign(that: FpLitExpr): BoolLitExpr {
        require(this.type == that.type)
        val left = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, this)
        val right = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, that)
        return Bool(this.hidden == that.hidden && exponent == that.exponent && significand == that.significand)
    }

    fun gt(that: FpLitExpr): BoolLitExpr {
        require(this.type == that.type)
        val left = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, this)
        val right = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, that)
        if (left.isNaN || right.isNaN) {
            return False()
        }
        return if (left.greaterThan(right)) {
            True()
        } else {
            False()
        }
    }

    fun lt(that: FpLitExpr): BoolLitExpr {
        require(this.type == that.type)
        val left = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, this)
        val right = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, that)
        if (left.isNaN || right.isNaN) {
            return False()
        }
        return if (left.lessThan(right)) {
            True()
        } else {
            False()
        }
    }

    fun geq(that: FpLitExpr): BoolLitExpr {
        require(this.type == that.type)
        val left = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, this)
        val right = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, that)
        if (left.isNaN || right.isNaN) {
            return False()
        }
        return if (left.greaterThanOrEqualTo(right)) {
            True()
        } else {
            False()
        }
    }

    fun leq(that: FpLitExpr): BoolLitExpr {
        require(this.type == that.type)
        val left = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, this)
        val right = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, that)
        if (left.isNaN || right.isNaN) {
            return False()
        }
        return if (left.lessThanOrEqualTo(right)) {
            True()
        } else {
            False()
        }
    }

    fun neq(that: FpLitExpr): BoolLitExpr {
        require(this.type == that.type)
        val left = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, this)
        val right = fpLitExprToBigFloat(FpRoundingMode.defaultRoundingMode, that)
        if (left.isNaN || right.isNaN) {
            return False()
        }
        return Bool(!(this.hidden == that.hidden && exponent == that.exponent && significand == that.significand))
    }

    override fun toString(): String = Utils.lispStringBuilder(if (hidden) "#b1" else "#b0")
        .add(exponent.toString())
        .add(significand.toString())
        .toString()

    override fun compareTo(other: FpType): Int = 0
}

