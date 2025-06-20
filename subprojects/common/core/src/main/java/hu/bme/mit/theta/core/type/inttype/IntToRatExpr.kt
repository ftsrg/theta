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

package hu.bme.mit.theta.core.type.inttype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.CastExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.rattype.RatLitExpr
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("IntToRat")
data class IntToRatExpr(
    override val op: Expr<IntType>
) : CastExpr<IntType, RatType>() {

    companion object {

        private const val OPERATOR_LABEL = "to_rat"

        @JvmStatic
        fun of(op: Expr<IntType>) = IntToRatExpr(op)

        @JvmStatic
        fun create(op: Expr<*>) = IntToRatExpr(cast(op, Int()))
    }

    override val type: RatType = Rat()
    override fun eval(`val`: Valuation): RatLitExpr {
        val opVal = op.eval(`val`) as IntLitExpr
        return opVal.toRat()
    }

    override fun of(op: Expr<IntType>): IntToRatExpr = Companion.of(op)
    override val operatorLabel: String get() = OPERATOR_LABEL
}

