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
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.utils.TypeUtils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("BvNot")
data class BvNotExpr(
    override val op: Expr<BvType>
) : UnaryExpr<BvType, BvType>() {

    companion object {
        private const val OPERATOR_LABEL = "bvnot"

        @JvmStatic
        fun of(op: Expr<BvType>) = BvNotExpr(op)

        @JvmStatic
        fun create(op: Expr<*>) = BvNotExpr(TypeUtils.castBv(op))
    }

    override val type: BvType get() = op.type

    override fun eval(`val`: Valuation): BvLitExpr {
        val opVal = op.eval(`val`) as BvLitExpr
        return opVal.not()
    }

    override fun of(op: Expr<BvType>): BvNotExpr = Companion.of(op)

    override val operatorLabel: String get() = OPERATOR_LABEL

    override fun toString(): String = super.toString()
}
