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
import hu.bme.mit.theta.core.type.inttype.IntType
import java.util.Objects
import java.util.Optional

class Dereference<A : Type, O : Type, T : Type>
private constructor(
  val array: Expr<A>,
  val offset: Expr<O>,
  uniqueness: Expr<IntType>?,
  override val type: T,
) : AbstractExpr<T>() {

  val uniquenessIdx: Optional<Expr<IntType>> = Optional.ofNullable(uniqueness)

  // TODO: this kills the stuck check
  fun withUniquenessExpr(expr: Expr<IntType>): Dereference<A, O, T> =
    keepSourceType(Dereference(array, offset, expr, type))

  override val arity: Int
    get() = 3

  override fun eval(valuation: Valuation): LitExpr<T> =
    throw IllegalStateException("Reference/Dereference expressions are not meant to be evaluated!")

  override val ops: List<Expr<*>>
    get() =
      if (uniquenessIdx.isPresent) listOf(array, offset, uniquenessIdx.get())
      else listOf(array, offset)

  override fun withOps(ops: List<Expr<*>>): Expr<T> {
    checkState(ops.size == 3 || ops.size == 2)
    @Suppress("UNCHECKED_CAST")
    return keepSourceType(
      Dereference(
        ops[0] as Expr<A>,
        ops[1] as Expr<O>,
        if (ops.size == 3) ops[2] as Expr<IntType> else null,
        type,
      )
    )
  }

  override fun hashCode(): Int = Objects.hash(array, offset, uniquenessIdx, type)

  override fun equals(other: Any?): Boolean =
    other is Dereference<*, *, *> &&
      array == other.array &&
      offset == other.offset &&
      uniquenessIdx == other.uniquenessIdx &&
      type == other.type

  override fun toString(): String {
    val base = Utils.lispStringBuilder(OPERATOR_LABEL).body().add(array).add(offset)
    uniquenessIdx.ifPresent { base.add(it) }
    return base.add(type).toString()
  }

  companion object {
    private const val OPERATOR_LABEL = "deref"

    @JvmStatic
    fun <A : Type, O : Type, T : Type> of(
      array: Expr<A>,
      offset: Expr<O>,
      type: T,
    ): Dereference<A, O, T> = Dereference(array, offset, null, type)
  }
}
