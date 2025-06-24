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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.LtExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("BvSLt")
data class BvSLtExpr(
    override val leftOp: Expr<BvType>,
    override val rightOp: Expr<BvType>
) : LtExpr<BvType>() {

    companion object {

        private const val OPERATOR_LABEL = "bvslt"

        @JvmStatic
        fun of(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSLtExpr(leftOp, rightOp)

        @JvmStatic
        fun create(leftOp: Expr<*>, rightOp: Expr<*>) = BvSLtExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
    }

    override fun eval(`val`: Valuation): LitExpr<BoolType> {
        val leftOpVal = leftOp.eval(`val`) as BvLitExpr
        val rightOpVal = rightOp.eval(`val`) as BvLitExpr
        return leftOpVal.slt(rightOpVal)
    }

    override fun of(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvSLtExpr = Companion.of(leftOp, rightOp)
    override val operatorLabel: String get() = OPERATOR_LABEL
    override fun toString(): String = super.toString()
}

