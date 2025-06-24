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

package hu.bme.mit.theta.core.type.bvtype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils.*
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import java.math.BigInteger
import kotlin.concurrent.Volatile

@Serializable
@SerialName("BvLit")
data class BvLitExpr(
    val value: BooleanArray,
    val signed: Boolean? = null
) : NullaryExpr<BvType>(), LitExpr<BvType>, Comparable<BvLitExpr> {

    init {
        require(value.isNotEmpty()) { "Bitvector must have positive size." }
    }

    companion object {

        private const val HASH_SEED: Int = 5624

        @JvmStatic
        fun of(value: BooleanArray, signed: Boolean? = null) = BvLitExpr(value, signed)
    }

    @Volatile
    @Transient
    private var hashCode = 0

    override val type: BvType get() = BvType(value.size, signed)
    override fun eval(`val`: Valuation): BvLitExpr = this

    fun concat(that: BvLitExpr): BvLitExpr {
        val concatenated = BooleanArray(this.type.size + that.type.size)
        for (i in 0 until this.type.size) concatenated[i] = this.value[i]
        for (i in 0 until that.type.size) concatenated[this.type.size + i] = that.value[i]
        return of(concatenated)
    }

    fun extract(from: IntLitExpr, until: IntLitExpr): BvLitExpr {
        val fromValue = from.value.toInt()
        val untilValue = until.value.toInt()
        require(fromValue >= 0 && untilValue >= 0 && untilValue > fromValue)
        val extracted = BooleanArray(untilValue - fromValue)
        for (i in extracted.indices) {
            extracted[extracted.size - i - 1] = this.value[this.value.size - (fromValue + i) - 1]
        }
        return of(extracted)
    }

    fun zext(extendType: BvType): BvLitExpr {
        require(extendType.size >= this.type.size)
        val extended = BooleanArray(extendType.size)
        for (i in this.value.indices) {
            extended[extended.size - i - 1] = this.value[this.value.size - i - 1]
        }
        for (i in 0 until extendType.size - this.type.size) {
            extended[i] = false
        }
        return of(extended)
    }

    fun sext(extendType: BvType): BvLitExpr {
        require(extendType.size >= this.type.size)
        val extended = BooleanArray(extendType.size)
        for (i in this.value.indices) {
            extended[extended.size - i - 1] = this.value[this.value.size - i - 1]
        }
        for (i in 0 until extendType.size - this.type.size) {
            extended[i] = this.value[0]
        }
        return of(extended)
    }

    fun add(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        var sum = neutralBvLitExprToBigInteger(this).add(neutralBvLitExprToBigInteger(that))
        sum = fitBigIntegerIntoNeutralDomain(sum, type.size)
        return bigIntegerToNeutralBvLitExpr(sum, type.size)
    }

    fun sub(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        var sub = neutralBvLitExprToBigInteger(this).subtract(neutralBvLitExprToBigInteger(that))
        sub = fitBigIntegerIntoNeutralDomain(sub, type.size)
        return bigIntegerToNeutralBvLitExpr(sub, type.size)
    }

    fun mul(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        var prod = neutralBvLitExprToBigInteger(this).multiply(neutralBvLitExprToBigInteger(that))
        prod = fitBigIntegerIntoNeutralDomain(prod, type.size)
        return bigIntegerToNeutralBvLitExpr(prod, type.size)
    }

    fun pos(): BvLitExpr {
        var pos = signedBvLitExprToBigInteger(this)
        pos = fitBigIntegerIntoSignedDomain(pos, type.size)
        return bigIntegerToSignedBvLitExpr(pos, type.size)
    }

    fun neg(): BvLitExpr {
        var neg = signedBvLitExprToBigInteger(this).negate()
        neg = fitBigIntegerIntoSignedDomain(neg, type.size)
        return bigIntegerToSignedBvLitExpr(neg, type.size)
    }

    fun udiv(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        var div = unsignedBvLitExprToBigInteger(this).divide(unsignedBvLitExprToBigInteger(that))
        div = fitBigIntegerIntoUnsignedDomain(div, type.size)
        return bigIntegerToUnsignedBvLitExpr(div, type.size)
    }

    fun sdiv(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        var div = signedBvLitExprToBigInteger(this).divide(signedBvLitExprToBigInteger(that))
        div = fitBigIntegerIntoSignedDomain(div, type.size)
        return bigIntegerToSignedBvLitExpr(div, type.size)
    }

    fun and(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        val and = neutralBvLitExprToBigInteger(this).and(neutralBvLitExprToBigInteger(that))
        return bigIntegerToNeutralBvLitExpr(and, type.size)
    }

    fun or(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        val or = neutralBvLitExprToBigInteger(this).or(neutralBvLitExprToBigInteger(that))
        return bigIntegerToNeutralBvLitExpr(or, type.size)
    }

    fun xor(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        val xor = neutralBvLitExprToBigInteger(this).xor(neutralBvLitExprToBigInteger(that))
        return bigIntegerToNeutralBvLitExpr(xor, type.size)
    }

    fun not(): BvLitExpr {
        val not = neutralBvLitExprToBigInteger(this).not()
        return bigIntegerToNeutralBvLitExpr(not, type.size)
    }

    fun shiftLeft(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        val shifted = value.copyOf(value.size)
        val shift = neutralBvLitExprToBigInteger(that)
        var i = BigInteger.ZERO
        while (i < shift) {
            for (j in 0 until shifted.size - 1) {
                shifted[j] = shifted[j + 1]
            }
            shifted[shifted.size - 1] = false
            i = i.add(BigInteger.ONE)
        }
        return of(shifted)
    }

    fun arithShiftRight(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        val shifted = value.copyOf(value.size)
        val insert = shifted[0]
        val shift = neutralBvLitExprToBigInteger(that)
        var i = BigInteger.ZERO
        while (i < shift) {
            for (j in shifted.size - 1 downTo 1) {
                shifted[j] = shifted[j - 1]
            }
            shifted[0] = insert
            i = i.add(BigInteger.ONE)
        }
        return of(shifted)
    }

    fun logicShiftRight(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        val shifted = value.copyOf(value.size)
        val shift = neutralBvLitExprToBigInteger(that)
        var i = BigInteger.ZERO
        while (i < shift) {
            for (j in shifted.size - 1 downTo 1) {
                shifted[j] = shifted[j - 1]
            }
            shifted[0] = false
            i = i.add(BigInteger.ONE)
        }
        return of(shifted)
    }

    fun rotateLeft(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        val shifted = value.copyOf(value.size)
        val shift = neutralBvLitExprToBigInteger(that)
        var i = BigInteger.ZERO
        while (i < shift) {
            val rotated = shifted[0]
            for (j in 0 until shifted.size - 1) {
                shifted[j] = shifted[j + 1]
            }
            shifted[shifted.size - 1] = rotated
            i = i.add(BigInteger.ONE)
        }
        return of(shifted)
    }

    fun rotateRight(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        val shifted = value.copyOf(value.size)
        val shift = neutralBvLitExprToBigInteger(that)
        var i = BigInteger.ZERO
        while (i < shift) {
            val rotated = shifted[shifted.size - 1]
            for (j in shifted.size - 1 downTo 1) {
                shifted[j] = shifted[j - 1]
            }
            shifted[0] = rotated
            i = i.add(BigInteger.ONE)
        }
        return of(shifted)
    }

    fun smod(that: BvLitExpr): BvLitExpr {
        require(this.type == that.type)
        // Always positive semantics:
        // 5 mod 3 = 2
        // 5 mod -3 = 2
        // -5 mod 3 = 1
        // -5 mod -3 = 1
        var result = signedBvLitExprToBigInteger(this).mod(signedBvLitExprToBigInteger(that))
        if (result < BigInteger.ZERO) {
            result = result.add(signedBvLitExprToBigInteger(that).abs())
        }
        require(result >= BigInteger.ZERO)
        return bigIntegerToSignedBvLitExpr(result, type.size)
    }

    fun urem(that: BvLitExpr): BvLitExpr {
        // Semantics:
        // 5 rem 3 = 2
        val thisInt = signedBvLitExprToBigInteger(this)
        val thatInt = signedBvLitExprToBigInteger(that)
        return bigIntegerToSignedBvLitExpr(thisInt.mod(thatInt), type.size)
    }

    fun srem(that: BvLitExpr): BvLitExpr {
        // Semantics:
        // 5 rem 3 = 2
        // 5 rem -3 = 2
        // -5 rem 3 = -1
        // -5 rem -3 = -1
        val thisInt = signedBvLitExprToBigInteger(this)
        val thatInt = signedBvLitExprToBigInteger(that)
        val thisAbs = thisInt.abs()
        val thatAbs = thatInt.abs()
        return when {
            thisInt < BigInteger.ZERO && thatInt < BigInteger.ZERO -> {
                bigIntegerToSignedBvLitExpr(thisAbs.mod(thatAbs).negate(), type.size)
            }

            thisInt >= BigInteger.ZERO && thatInt < BigInteger.ZERO -> {
                bigIntegerToSignedBvLitExpr(thisAbs.mod(thatAbs), type.size)
            }

            thisInt < BigInteger.ZERO && thatInt >= BigInteger.ZERO -> {
                bigIntegerToSignedBvLitExpr(thisAbs.mod(thatAbs).negate(), type.size)
            }

            else -> {
                bigIntegerToSignedBvLitExpr(thisInt.mod(thatInt), type.size)
            }
        }
    }

    fun eq(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(this.value.contentEquals(that.value))
    }

    fun neq(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(!this.value.contentEquals(that.value))
    }

    fun ult(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(
            unsignedBvLitExprToBigInteger(this) < unsignedBvLitExprToBigInteger(that)
        )
    }

    fun ule(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(
            unsignedBvLitExprToBigInteger(this) <= unsignedBvLitExprToBigInteger(that)
        )
    }

    fun ugt(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(
            unsignedBvLitExprToBigInteger(this) > unsignedBvLitExprToBigInteger(that)
        )
    }

    fun uge(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(
            unsignedBvLitExprToBigInteger(this) >= unsignedBvLitExprToBigInteger(that)
        )
    }

    fun slt(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(
            signedBvLitExprToBigInteger(this) < signedBvLitExprToBigInteger(that)
        )
    }

    fun sle(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(
            signedBvLitExprToBigInteger(this) <= signedBvLitExprToBigInteger(that)
        )
    }

    fun sgt(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(
            signedBvLitExprToBigInteger(this) > signedBvLitExprToBigInteger(that)
        )
    }

    fun sge(that: BvLitExpr): BoolLitExpr {
        require(this.type == that.type)
        return Bool(
            signedBvLitExprToBigInteger(this) >= signedBvLitExprToBigInteger(that)
        )
    }

    override fun compareTo(other: BvLitExpr): Int {
        // Use unsigned comparison for ordering
        return unsignedBvLitExprToBigInteger(this).compareTo(unsignedBvLitExprToBigInteger(other))
    }


    override fun hashCode(): Int {
        var result = hashCode
        if (result == 0) {
            result = HASH_SEED
            result = 31 * result + value.contentHashCode()
            hashCode = result
        }
        return result
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) {
            return true
        } else if (other != null && this.javaClass == other.javaClass) {
            val that = other as BvLitExpr
            return value.contentEquals(that.value)
        } else {
            return false
        }
    }

    override fun toString(): String {
        val sb = StringBuilder()
        //        sb.append(getType().getSize());
        sb.append("#b")
        for (bit in value) {
            sb.append(if (bit) "1" else "0")
        }
        return sb.toString()
    }
}
