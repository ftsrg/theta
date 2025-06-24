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
import hu.bme.mit.theta.core.type.abstracttype.MulExpr
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import java.math.BigInteger

@Serializable
@SerialName("RatMul")
data class RatMulExpr(
    override val ops: List<Expr<RatType>>
) : MulExpr<RatType>() {

    companion object {

        private const val OPERATOR_LABEL = "*"

        @JvmStatic
        fun of(ops: Iterable<Expr<RatType>>) = RatMulExpr(ops.toList())

        @JvmStatic
        fun create(ops: List<Expr<*>>) = RatMulExpr(ops.map { cast(it, Rat()) })
    }

    override val type: RatType = Rat()
    override fun eval(`val`: Valuation): RatLitExpr {
        var prodNum = BigInteger.ONE
        var prodDenom = BigInteger.ONE
        ops.forEach { op ->
            val opVal = op.eval(`val`) as RatLitExpr
            prodNum *= opVal.num
            prodDenom *= opVal.denom
        }
        return Rat(prodNum, prodDenom)
    }

    override fun of(ops: List<Expr<RatType>>): RatMulExpr =
        Companion.of(ops)

    override val operatorLabel: String get() = OPERATOR_LABEL
}

