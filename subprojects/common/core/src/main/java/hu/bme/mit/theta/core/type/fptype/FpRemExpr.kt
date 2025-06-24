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
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.utils.FpUtils.*
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpRem")
data class FpRemExpr(
    override val leftOp: Expr<FpType>,
    override val rightOp: Expr<FpType>
) : BinaryExpr<FpType, FpType>() {

    init {
        checkAllTypesEqual(leftOp, rightOp)
    }

    companion object {

        private const val OPERATOR_LABEL = "fprem"

        @JvmStatic
        fun of(leftOp: Expr<FpType>, rightOp: Expr<FpType>) =
            FpRemExpr(leftOp, rightOp)

        @JvmStatic
        fun create(leftOp: Expr<*>, rightOp: Expr<*>) =
            FpRemExpr(castFp(leftOp), castFp(rightOp))
    }

    override val type: FpType get() = leftOp.type

    override fun eval(`val`: Valuation): FpLitExpr {
        val leftOpVal = leftOp.eval(`val`) as FpLitExpr
        val rightOpVal = rightOp.eval(`val`) as FpLitExpr
        val leftFloat = fpLitExprToBigFloat(null, leftOpVal)
        val rightFloat = fpLitExprToBigFloat(null, rightOpVal)
        val remainder = leftFloat.remainder(rightFloat, getMathContext(this.type, null))
        return bigFloatToFpLitExpr(remainder, this.type)
    }

    override fun of(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpRemExpr =
        Companion.of(leftOp, rightOp)

    override val operatorLabel: String get() = OPERATOR_LABEL

    override fun toString(): String = super.toString()
}

