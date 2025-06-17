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
package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract class for additive expressions with multiple operands.
 */
@Serializable
abstract class AddExpr<ExprType : Additive<ExprType>> : MultiaryExpr<ExprType, ExprType>() {

    companion object {

        fun <ExprType : Additive<ExprType>> create2(ops: List<Expr<*>>): AddExpr<*> {
            require(ops.isNotEmpty())
            @Suppress("UNCHECKED_CAST")
            val type = ops[0].type as ExprType
            return type.Add(ops.map { cast(it, type) })
        }
    }
}
