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
import java.util.function.Function

/**
 * An expression. The hierarchy is sealed: expressions defined outside this package extend
 * [ForeignExpr] (or [ForeignLitExpr] for literals).
 */
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

  /**
   * The type of this expression in the source language, if known. It is not part of the
   * expression's meaning: [equals] and [hashCode] ignore it, and operand rewrites ([withOps], [map]
   * and the classes' `with` methods) keep it.
   */
  val sourceType: SourceType?

  /** A copy of this expression with [sourceType] attached (or this expression if unchanged). */
  fun withSourceType(sourceType: SourceType?): Expr<ExprType>
}

/**
 * The extension point of the sealed [Expr] hierarchy, for expressions defined outside of it (e.g.
 * frontend-internal placeholders). Code switching over [Expr] handles all of them with one branch.
 */
abstract class ForeignExpr<ExprType : Type> : AbstractExpr<ExprType>()

/** A [ForeignExpr] that is also a literal. */
abstract class ForeignLitExpr<ExprType : Type> : ForeignExpr<ExprType>(), LitExpr<ExprType>
