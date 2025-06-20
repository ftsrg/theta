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

import hu.bme.mit.theta.core.model.Valuation
import kotlinx.serialization.Polymorphic
import kotlinx.serialization.Serializable

/**
 * Base class for all expressions in the Theta framework.
 *
 * @param ExprType The type of the expression, must be a subtype of [Type]
 */
@Polymorphic
interface Expr<ExprType : Type> {

    /**
     * Returns the arity (number of operands) of this expression.
     */
    val arity: Int
        get() = ops.size

    /**
     * Returns the type of this expression.
     */
    val type: ExprType

    /**
     * Returns the list of operands of this expression.
     */
    val ops: List<Expr<*>>

    /**
     * Evaluates this expression with the given valuation.
     * @param val The valuation to use for evaluation
     * @return The result of the evaluation as a literal expression
     */
    fun eval(`val`: Valuation): LitExpr<ExprType>

    /**
     * Checks if this expression is invalid.
     * An expression is invalid if any of its operands are invalid.
     */
    val isInvalid: Boolean
        get() = ops.any { it.isInvalid }

    /**
     * Creates a new expression of the same type with the given operands.
     * @param ops The new operands
     * @return A new expression with the given operands
     */
    fun withOps(ops: List<Expr<*>>): Expr<ExprType>

    /**
     * Applies the given function to each operand of this expression and returns a new expression
     * with the results.
     * @param function The function to apply to each operand
     * @return A new expression with the transformed operands
     */
    fun map(function: (Expr<*>) -> Expr<*>): Expr<ExprType> = withOps(ops.map(function))
}
