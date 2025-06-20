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
 * Base class for expressions with two operands (binary expressions).
 *
 * @param OpType The type of the operands
 * @param ExprType The type of the expression
 */
@Serializable
abstract class BinaryExpr<OpType : Type, ExprType : Type> : Expr<ExprType> {

    protected abstract val leftOp: Expr<OpType>
    protected abstract val rightOp: Expr<OpType>

    override val ops: List<Expr<OpType>> get() = listOf(leftOp, rightOp)

    abstract val operatorLabel: String

    override fun withOps(ops: List<Expr<*>>): Expr<ExprType> {
        require(ops.size == 2) { "Operands must have size 2 for binary expression" }
        val opType = leftOp.type
        val newLeftOp = TypeUtils.cast(ops[0], opType)
        val newRightOp = TypeUtils.cast(ops[1], opType)
        return with(newLeftOp, newRightOp)
    }

    open fun with(leftOp: Expr<OpType>, rightOp: Expr<OpType>): BinaryExpr<OpType, ExprType> =
        if (leftOp == this.leftOp && rightOp == this.rightOp) {
            this
        } else {
            of(leftOp, rightOp)
        }

    protected abstract fun of(leftOp: Expr<OpType>, rightOp: Expr<OpType>): BinaryExpr<OpType, ExprType>

    open fun withLeftOp(leftOp: Expr<OpType>): BinaryExpr<OpType, ExprType> = with(leftOp, rightOp)

    open fun withRightOp(rightOp: Expr<OpType>): BinaryExpr<OpType, ExprType> = with(leftOp, rightOp)

    override fun toString(): String = Utils.lispStringBuilder(operatorLabel)
        .body()
        .add(leftOp)
        .add(rightOp)
        .toString()
}
