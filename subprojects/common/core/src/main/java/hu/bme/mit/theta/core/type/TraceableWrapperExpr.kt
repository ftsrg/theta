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

import com.google.common.base.Preconditions.checkArgument
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Information tying an expression to its origin, e.g. its type in the source language. Core carries
 * it in [TraceableWrapperExpr] but never interprets it.
 */
interface TraceabilityInfo {
  /** What an expression rebuilt from the annotated one keeps; null keeps nothing. */
  fun afterRewrite(): TraceabilityInfo? = this
}

/**
 * [expr] annotated with [info]. The wrapper stands for [expr]: it has the same type and value,
 * prints the same, and is equal to (and hashes like) [expr]; rewriting its operand keeps what
 * [TraceabilityInfo.afterRewrite] allows. Analyses never see it, as the model is stripped of
 * wrappers before verification.
 */
@Serializable
class TraceableWrapperExpr<ExprType : Type>
private constructor(val expr: Expr<ExprType>, val info: TraceabilityInfo) : Expr<ExprType> {

  override val arity: Int
    get() = 1

  override val type: ExprType
    get() = expr.type

  override fun eval(valuation: Valuation): LitExpr<ExprType> = expr.eval(valuation)

  override val ops: List<Expr<ExprType>>
    get() = ImmutableList.of(expr)

  override val isInvalid: Boolean
    get() = expr.isInvalid

  override fun withOps(ops: List<Expr<*>>): Expr<ExprType> {
    checkArgument(ops.size == 1)
    return with(cast(ops[0], expr.type))
  }

  fun with(expr: Expr<ExprType>): Expr<ExprType> =
    when {
      expr === this.expr -> this
      DROP_ON_REWRITE -> expr
      else -> info.afterRewrite()?.let { of(expr, it) } ?: expr
    }

  override fun equals(other: Any?): Boolean =
    expr == if (other is TraceableWrapperExpr<*>) other.expr else other

  override fun hashCode(): Int = expr.hashCode()

  override fun toString(): String = expr.toString()

  companion object {
    // Validation aid: a rewritten operand loses its info, whatever afterRewrite says.
    private val DROP_ON_REWRITE = java.lang.Boolean.getBoolean("theta.traceability.dropOnRewrite")

    /** [expr] (without its own wrappers) annotated with [info]. */
    @JvmStatic
    fun <ExprType : Type> of(
      expr: Expr<ExprType>,
      info: TraceabilityInfo,
    ): TraceableWrapperExpr<ExprType> = TraceableWrapperExpr(expr.unwrapTraceable(), info)
  }
}
