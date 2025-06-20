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
package hu.bme.mit.theta.core.type.anytype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Represents an if-then-else expression.
 *
 * @param ExprType The type of the expression
 */
@Serializable
@SerialName("Ite")
data class IteExpr<ExprType : Type>(
    val cond: Expr<BoolType>,
    val then: Expr<ExprType>,
    val elze: Expr<ExprType>
) : Expr<ExprType> {

    companion object {

        private const val OPERATOR_LABEL = "ite"

        @JvmStatic
        fun <ExprType : Type> of(
            cond: Expr<BoolType>,
            then: Expr<ExprType>,
            elze: Expr<ExprType>
        ): IteExpr<ExprType> = IteExpr(cond, then, elze)

        @JvmStatic
        fun <ExprType : Type> create(
            cond: Expr<*>,
            then: Expr<*>,
            elze: Expr<*>
        ): IteExpr<ExprType> {
            val newCond = cast(cond, Bool())

            @Suppress("UNCHECKED_CAST")
            val newThen = then as Expr<ExprType>
            val newElze = cast(elze, newThen.type)
            return of(newCond, newThen, newElze)
        }
    }

    override val type: ExprType = then.type

    override val arity: Int = 3

    override val ops: List<Expr<*>> = listOf(cond, then, elze)

    override fun eval(`val`: Valuation): LitExpr<ExprType> =
        if ((cond.eval(`val`) as BoolLitExpr).value) {
            then.eval(`val`)
        } else {
            elze.eval(`val`)
        }

    override fun withOps(ops: List<Expr<*>>): IteExpr<ExprType> {
        require(ops.size == 3) { "Operands must have size 3 for Ite expression" }
        val newCond = cast(ops[0], Bool())
        val newThen = cast(ops[1], type)
        val newElze = cast(ops[2], type)
        return with(newCond, newThen, newElze)
    }

    fun with(cond: Expr<BoolType>, then: Expr<ExprType>, elze: Expr<ExprType>): IteExpr<ExprType> =
        if (this.cond === cond && this.then === then && this.elze === elze) {
            this
        } else {
            of(cond, then, elze)
        }

    fun withCond(cond: Expr<BoolType>): IteExpr<ExprType> = with(cond, then, elze)

    fun withThen(then: Expr<ExprType>): IteExpr<ExprType> = with(cond, then, elze)

    fun withElse(elze: Expr<ExprType>): IteExpr<ExprType> = with(cond, then, elze)

    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL)
        .add(cond)
        .add(then)
        .add(elze)
        .toString()
}
