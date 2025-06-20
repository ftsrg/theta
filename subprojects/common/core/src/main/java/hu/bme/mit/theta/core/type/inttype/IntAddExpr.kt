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
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import java.math.BigInteger

@Serializable
@SerialName("IntAdd")
data class IntAddExpr(
    override val ops: List<Expr<IntType>>
) : AddExpr<IntType>() {

    companion object {

        internal const val OPERATOR_LABEL = "+"

        @JvmStatic
        fun of(ops: Iterable<Expr<IntType>>) = IntAddExpr(ops.toList())

        @JvmStatic
        fun create(ops: List<Expr<*>>) = IntAddExpr(ops.map { cast(it, Int()) })
    }

    override val type: IntType = Int()
    override fun eval(`val`: Valuation): IntLitExpr {
        var sum = BigInteger.ZERO
        ops.forEach { op ->
            val opVal = op.eval(`val`) as IntLitExpr
            sum = sum.add(opVal.value)
        }
        return Int(sum)
    }

    override fun of(ops: List<Expr<IntType>>): IntAddExpr =
        Companion.of(ops)

    override val operatorLabel: String get() = OPERATOR_LABEL
}

