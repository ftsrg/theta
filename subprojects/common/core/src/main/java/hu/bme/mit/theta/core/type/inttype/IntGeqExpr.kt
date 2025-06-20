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
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("IntGeq")
data class IntGeqExpr(
    override val leftOp: Expr<IntType>,
    override val rightOp: Expr<IntType>
) : GeqExpr<IntType>() {

    companion object {

        internal const val OPERATOR_LABEL = ">="
        @JvmStatic
        fun of(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntGeqExpr(leftOp, rightOp)
        @JvmStatic
        fun create(leftOp: Expr<*>, rightOp: Expr<*>) = IntGeqExpr(cast(leftOp, Int()), cast(rightOp, Int()))
    }

    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): BoolLitExpr {
        val leftOpVal = leftOp.eval(`val`) as IntLitExpr
        val rightOpVal = rightOp.eval(`val`) as IntLitExpr
        return leftOpVal.geq(rightOpVal)
    }

    override fun of(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntGeqExpr =
        Companion.of(leftOp, rightOp)

    override val operatorLabel: String get() = OPERATOR_LABEL
}

