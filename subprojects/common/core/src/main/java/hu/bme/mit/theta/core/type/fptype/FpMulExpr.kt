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
import hu.bme.mit.theta.core.type.abstracttype.MulExpr
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpMul")
data class FpMulExpr(
    val roundingMode: FpRoundingMode,
    override val ops: List<Expr<FpType>>
) : MulExpr<FpType>() {

    init {
        checkAllTypesEqual(ops)
    }

    companion object {

        private const val OPERATOR_LABEL = "fpmul"

        @JvmStatic
        fun of(roundingMode: FpRoundingMode, ops: Iterable<Expr<FpType>>) =
            FpMulExpr(roundingMode, ops.toList())

        @JvmStatic
        fun create(roundingMode: FpRoundingMode, ops: List<Expr<*>>) =
            FpMulExpr(roundingMode, ops.map { castFp(it) })
    }

    override val type: FpType get() = ops[0].type

    override fun eval(`val`: Valuation): FpLitExpr =
        ops.drop(1).fold(ops[0].eval(`val`) as FpLitExpr) { acc, op ->
            acc.mul(roundingMode, op.eval(`val`) as FpLitExpr)
        }

    override fun new(ops: List<Expr<FpType>>): FpMulExpr = of(roundingMode, ops)

    override val operatorLabel: String get() = OPERATOR_LABEL

    override fun toString(): String = super.toString()
}

