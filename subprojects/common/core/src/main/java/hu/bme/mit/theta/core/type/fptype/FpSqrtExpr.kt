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
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.utils.FpUtils.*
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpSqrt")
data class FpSqrtExpr(
    val roundingMode: FpRoundingMode,
    override val op: Expr<FpType>
) : UnaryExpr<FpType, FpType>() {

    companion object {

        private const val OPERATOR_LABEL = "fpsqrt"

        @JvmStatic
        fun of(roundingMode: FpRoundingMode, op: Expr<FpType>) =
            FpSqrtExpr(roundingMode, op)

        @JvmStatic
        fun create(roundingMode: FpRoundingMode, op: Expr<*>) =
            FpSqrtExpr(roundingMode, castFp(op))
    }

    override val type: FpType get() = op.type

    override fun eval(`val`: Valuation): LitExpr<FpType> {
        val opVal = op.eval(`val`) as FpLitExpr
        val sqrt = fpLitExprToBigFloat(roundingMode, opVal)
            .sqrt(getMathContext(type, roundingMode))
        return bigFloatToFpLitExpr(sqrt, type)
    }

    override fun of(op: Expr<FpType>): FpSqrtExpr =
        Companion.of(roundingMode, op)

    override val operatorLabel: String get() = OPERATOR_LABEL

    override fun toString(): String = super.toString()
}

