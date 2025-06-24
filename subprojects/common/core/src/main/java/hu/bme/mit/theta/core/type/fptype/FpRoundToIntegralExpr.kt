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

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import org.kframework.mpfr.BinaryMathContext

@Serializable
@SerialName("FpRoundToIntegral")
data class FpRoundToIntegralExpr(
    val roundingMode: FpRoundingMode,
    override val op: Expr<FpType>
) : UnaryExpr<FpType, FpType>() {
    companion object {
        private const val OPERATOR_LABEL = "fproundtoint"

        @JvmStatic
        fun of(roundingMode: FpRoundingMode, op: Expr<FpType>) =
            FpRoundToIntegralExpr(roundingMode, op)

        @JvmStatic
        fun create(roundingMode: FpRoundingMode, op: Expr<*>) =
            FpRoundToIntegralExpr(roundingMode, castFp(op))
    }

    override val type: FpType get() = op.type

    override fun eval(`val`: Valuation): FpLitExpr {
        val opVal = op.eval(`val`) as FpLitExpr
        val value = FpUtils.fpLitExprToBigFloat(roundingMode, opVal)
        val bigInteger = value.toBigInteger()
        var round =
            value.round(
                BinaryMathContext(
                    bigInteger.bitLength(),
                    opVal.type.exponent,
                    FpUtils.getMathContextRoundingMode(roundingMode)
                )
            )
        round = round.round(FpUtils.getMathContext(type, roundingMode))
        val fpLitExpr = FpUtils.bigFloatToFpLitExpr(round, this.type)
        return fpLitExpr
    }

    override fun new(op: Expr<FpType>): FpRoundToIntegralExpr =
        of(roundingMode, op)

    override val operatorLabel: String get() = OPERATOR_LABEL

    override fun toString(): String = super.toString()
}

