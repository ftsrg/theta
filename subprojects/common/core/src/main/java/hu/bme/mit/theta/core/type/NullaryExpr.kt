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

import kotlinx.serialization.Serializable

/**
 * Base class for expressions with no operands (nullary expressions).
 *
 * @param ExprType The type of the expression, must be a subtype of [Type]
 */
@Serializable
abstract class NullaryExpr<ExprType : Type> : Expr<ExprType> {
    override val arity: Int get() = 0
    
    override val ops: List<Expr<*>>
        get() = emptyList()

    override fun withOps(ops: List<Expr<*>>): Expr<ExprType> {
        require(ops.isEmpty()) { "Operands must be empty for nullary expression" }
        return this
    }
}
