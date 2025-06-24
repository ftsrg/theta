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
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpAbs")
data class FpAbsExpr(
    override val op: Expr<FpType>
) : UnaryExpr<FpType, FpType>() {
    companion object {
        private const val OPERATOR_LABEL = "fpabs"

        @JvmStatic
        fun of(op: Expr<FpType>) = FpAbsExpr(op)

        @JvmStatic
        fun create(op: Expr<*>) = FpAbsExpr(castFp(op))
    }

    override val type: FpType get() = op.type

    override fun eval(`val`: Valuation): FpLitExpr {
        val opVal = op.eval(`val`) as FpLitExpr
        return if (opVal.hidden) {
            opVal.neg()
        } else {
            opVal
        }
    }

    override fun of(op: Expr<FpType>): FpAbsExpr = Companion.of(op)

    override val operatorLabel: String get() = OPERATOR_LABEL

    override fun toString(): String = super.toString()
}

