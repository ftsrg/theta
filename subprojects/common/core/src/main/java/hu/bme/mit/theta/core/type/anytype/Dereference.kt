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
import hu.bme.mit.theta.core.type.inttype.IntType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Represents a dereference expression for array access.
 *
 * @param A The array type
 * @param O The offset type
 * @param T The element type
 * @property array The array expression
 * @property offset The offset expression
 * @property type The type of the dereferenced element
 * @property uniquenessIdx Optional uniqueness index for SMT encoding
 */
@Serializable
@SerialName("Dereference")
data class Dereference<A : Type, O : Type, T : Type>(
    val array: Expr<A>,
    val offset: Expr<O>,
    override val type: T,
    val uniquenessIdx: Expr<IntType>? = null
) : Expr<T> {

    companion object {

        private const val OPERATOR_LABEL = "deref"

        @JvmStatic
        fun <A : Type, O : Type, T : Type> of(
            array: Expr<A>,
            offset: Expr<O>,
            type: T
        ): Dereference<A, O, T> = Dereference(array, offset, type)

        @JvmStatic
        private fun <A : Type, O : Type, T : Type> of(
            array: Expr<A>,
            offset: Expr<O>,
            uniqueness: Expr<IntType>,
            type: T
        ): Dereference<A, O, T> = Dereference(array, offset, type, uniqueness)
    }

    fun withUniquenessExpr(expr: Expr<IntType>): Dereference<A, O, T> =
        of(array, offset, expr, type)

    override val arity: Int = 3

    override val ops: List<Expr<*>> =
        if (uniquenessIdx != null) listOf(array, offset, uniquenessIdx)
        else listOf(array, offset)

    override fun eval(`val` : Valuation): LitExpr<T> =
        throw IllegalStateException("Reference/Dereference expressions are not meant to be evaluated!")

    @Suppress("UNCHECKED_CAST")
    override fun withOps(ops: List<Expr<*>>): Expr<T> {
        require(ops.size == 2 || ops.size == 3) { "Dereference must have 2 or 3 operands" }
        return when (ops.size) {
            2 -> of(ops[0] as Expr<A>, ops[1] as Expr<O>, type)
            else -> of(ops[0] as Expr<A>, ops[1] as Expr<O>, ops[2] as Expr<IntType>, type)
        }
    }

    override fun toString(): String =
        Utils.lispStringBuilder(OPERATOR_LABEL)
            .body()
            .addAll(ops)
            .add(type)
            .toString()
}
