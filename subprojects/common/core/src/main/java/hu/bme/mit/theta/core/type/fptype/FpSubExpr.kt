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
import hu.bme.mit.theta.core.type.abstracttype.SubExpr
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpSub")
data class FpSubExpr(
    val roundingMode: FpRoundingMode,
    override val leftOp: Expr<FpType>,
    override val rightOp: Expr<FpType>
) : SubExpr<FpType>() {

    init {
        checkAllTypesEqual(leftOp, rightOp)
    }

    companion object {

        private const val OPERATOR_LABEL = "fpsub"

        @JvmStatic
        fun of(roundingMode: FpRoundingMode, leftOp: Expr<FpType>, rightOp: Expr<FpType>) =
            FpSubExpr(roundingMode, leftOp, rightOp)

        @JvmStatic
        fun create(roundingMode: FpRoundingMode, leftOp: Expr<*>, rightOp: Expr<*>) =
            FpSubExpr(roundingMode, castFp(leftOp), castFp(rightOp))
    }

    override val type: FpType get() = leftOp.type

    override fun eval(`val`: Valuation): FpLitExpr {
        val leftOpVal = leftOp.eval(`val`) as FpLitExpr
        val rightOpVal = rightOp.eval(`val`) as FpLitExpr
        return leftOpVal.sub(roundingMode, rightOpVal)
    }

    override fun of(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpSubExpr =
        Companion.of(roundingMode, leftOp, rightOp)

    override val operatorLabel: String get() = OPERATOR_LABEL

    override fun toString(): String = super.toString()
}

