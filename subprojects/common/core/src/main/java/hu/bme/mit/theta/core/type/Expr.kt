/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.serialization.ExprReferenceSerializer
import java.util.function.Function
import kotlinx.serialization.Serializable

/**
 * An expression. The hierarchy is sealed: expressions defined outside this package extend
 * [ForeignExpr] (or [ForeignLitExpr] for literals).
 */
@Serializable(with = ExprReferenceSerializer::class)
sealed interface Expr<ExprType : Type> {

  val arity: Int

  val type: ExprType

  fun eval(valuation: Valuation): LitExpr<ExprType>

  val ops: List<@JvmWildcard Expr<*>>

  val isInvalid: Boolean
    get() = ops.any { it.isInvalid }

  fun withOps(ops: List<Expr<*>>): Expr<ExprType>

  fun map(function: Function<in Expr<*>, out Expr<*>>): Expr<ExprType> =
    withOps(ops.map { function.apply(it) })
}

/**
 * The extension point of the sealed [Expr] hierarchy, for expressions defined outside of it (e.g.
 * frontend-internal placeholders). Code switching over [Expr] handles all of them with one branch.
 */
abstract class ForeignExpr<ExprType : Type> : Expr<ExprType>

/** A [ForeignExpr] that is also a literal. */
abstract class ForeignLitExpr<ExprType : Type> : ForeignExpr<ExprType>(), LitExpr<ExprType>
