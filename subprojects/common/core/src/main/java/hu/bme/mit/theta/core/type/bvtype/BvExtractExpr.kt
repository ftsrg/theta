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

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.core.utils.TypeUtils.castBv
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("BvExtract")
data class BvExtractExpr(
    val bitvec: Expr<BvType>,
    val from: IntLitExpr,
    val until: IntLitExpr
) : Expr<BvType> {

    companion object {

        private const val OPERATOR_LABEL = "extract"

        @JvmStatic
        fun of(bitvec: Expr<BvType>, from: IntLitExpr, until: IntLitExpr) = BvExtractExpr(bitvec, from, until)

        @JvmStatic
        fun create(bitvec: Expr<*>, from: Expr<*>, until: Expr<*>): BvExtractExpr {
            val newBitvec = castBv(bitvec)
            val newFrom = TypeUtils.cast(from, Int()) as IntLitExpr
            val newUntil = TypeUtils.cast(until, Int()) as IntLitExpr
            return of(newBitvec, newFrom, newUntil)
        }
    }

    override val arity: Int = 3
    override val type: BvType = BvType.of(until.value.subtract(from.value).toInt())
    override val ops: List<Expr<*>> = listOf(bitvec, from, until)

    override fun eval(`val`: Valuation): BvLitExpr {
        val bitvecVal = bitvec.eval(`val`) as BvLitExpr
        return bitvecVal.extract(from, until)
    }

    override fun withOps(ops: List<Expr<*>>): Expr<BvType> {
        require(ops.size == 3)
        val newBitvec = castBv(ops[0])
        val newFrom = TypeUtils.cast(ops[1], Int()) as IntLitExpr
        val newUntil = TypeUtils.cast(ops[2], Int()) as IntLitExpr

        return if (bitvec == newBitvec && from == newFrom && until == newUntil) {
            this
        } else {
            of(newBitvec, newFrom, newUntil)
        }
    }

    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL)
        .body()
        .add(bitvec)
        .add(from)
        .add(until)
        .toString()
}

