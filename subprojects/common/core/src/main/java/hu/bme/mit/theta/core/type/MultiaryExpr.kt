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
 * Base class for expressions with multiple operands of the same type.
 *
 * @param OpType The type of the operands
 * @param ExprType The type of the expression
 */
@Serializable
abstract class MultiaryExpr<OpType : Type, ExprType : Type> : Expr<ExprType> {

    abstract override val ops: List<Expr<OpType>>

    abstract val operatorLabel: String

    override fun withOps(ops: List<Expr<*>>): MultiaryExpr<OpType, ExprType> {
        if (ops.isEmpty()) {
            return with(listOf())
        } else {
            val opType: OpType = this.ops[0].type
            val newOps: List<Expr<OpType>> = ops.map { op: Expr<*> -> TypeUtils.cast(op, opType) }
            return with(newOps)
        }
    }

    override fun toString(): String = Utils.lispStringBuilder(operatorLabel).body().addAll(ops).toString()

    open fun with(ops: Iterable<Expr<OpType>>): MultiaryExpr<OpType, ExprType> =
        if (ops.toList() == this.ops) {
            this
        } else {
            new(ops.toList())
        }

    protected abstract fun new(ops: List<Expr<OpType>>): MultiaryExpr<OpType, ExprType>
}
