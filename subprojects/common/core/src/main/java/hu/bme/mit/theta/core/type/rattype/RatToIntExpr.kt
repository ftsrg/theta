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

package hu.bme.mit.theta.core.type.rattype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("RatToInt")
data class RatToIntExpr(
    override val op: Expr<RatType>
) : UnaryExpr<RatType, IntType>() {

    companion object {

        private const val OPERATOR_LABEL = "to_int"

        @JvmStatic
        fun of(op: Expr<RatType>) = RatToIntExpr(op)

        @JvmStatic
        fun create(op: Expr<*>) = RatToIntExpr(cast(op, Rat()))
    }

    override val type: IntType = Int()
    override val operatorLabel: String get() = OPERATOR_LABEL
    override fun eval(`val`: Valuation): IntLitExpr {
        val opVal = op.eval(`val`) as RatLitExpr
        return opVal.toInt()
    }

    override fun of(op: Expr<RatType>): RatToIntExpr = Companion.of(op)
    override fun toString(): String = super.toString()
}

