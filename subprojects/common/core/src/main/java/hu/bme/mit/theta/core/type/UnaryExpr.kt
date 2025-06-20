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
package hu.bme.mit.theta.core.type

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.utils.TypeUtils
import kotlinx.serialization.Serializable

/**
 * Base class for expressions with a single operand (unary expressions).
 *
 * @param ExprType The type of the expression, must be a subtype of [Type]
 * @param OpType The type of the operand
 */
@Serializable
abstract class UnaryExpr<OpType : Type, ExprType : Type> : Expr<ExprType> {

    abstract val op: Expr<OpType>

    override val arity: Int get() = 1

    override val ops: List<Expr<*>>
        get() = listOf(op)

    override fun withOps(ops: List<Expr<*>>): Expr<ExprType> {
        require(ops.size == 1) { "Operands must have size 1 for unary expression" }
        val opType = op.type
        val newOp = TypeUtils.cast(ops[0], opType)
        return with(newOp)
    }

    override fun toString(): String = Utils.lispStringBuilder(operatorLabel).body().add(op).toString()

    open fun with(op: Expr<OpType>): UnaryExpr<OpType, ExprType> =
        if (op == this.op) this else of(op)

    protected abstract fun of(op: Expr<OpType>): UnaryExpr<OpType, ExprType>

    protected abstract val operatorLabel: String
}
