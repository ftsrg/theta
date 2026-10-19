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

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import java.util.Objects

class Reference<A : Type, T : Type> private constructor(val expr: Expr<T>, override val type: A) :
  AbstractExpr<A>() {

  override val arity: Int
    get() = 1

  override fun eval(valuation: Valuation): LitExpr<A> =
    throw IllegalStateException("Reference/Dereference expressions are not meant to be evaluated!")

  override val ops: List<Expr<*>>
    get() = listOf(expr)

  override fun withOps(ops: List<Expr<*>>): Expr<A> {
    checkState(ops.size == 1)
    @Suppress("UNCHECKED_CAST") return keepSourceType(of(ops[0] as Expr<T>, type))
  }

  override fun hashCode(): Int = Objects.hash(expr, type)

  override fun equals(other: Any?): Boolean =
    other is Reference<*, *> && expr == other.expr && type == other.type

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(expr).add(type).toString()

  companion object {
    private const val OPERATOR_LABEL = "ref"

    @JvmStatic
    fun <A : Type, T : Type> of(expr: Expr<T>, type: A): Reference<A, T> = Reference(expr, type)
  }
}
