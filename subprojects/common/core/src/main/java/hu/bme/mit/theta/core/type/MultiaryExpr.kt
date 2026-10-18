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

import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.utils.TypeUtils

sealed class MultiaryExpr<OpType : Type, ExprType : Type>
protected constructor(ops: Iterable<Expr<OpType>>) : AbstractExpr<ExprType>() {

  final override val ops: List<Expr<OpType>> = ImmutableList.copyOf(ops)

  @Volatile private var hashCode = 0

  final override val arity: Int
    get() = ops.size

  override fun withOps(ops: List<Expr<*>>): MultiaryExpr<OpType, ExprType> =
    if (ops.isEmpty()) {
      with(ImmutableList.of())
    } else {
      val opType = this.ops[0].type
      with(ops.map { TypeUtils.cast(it, opType) })
    }

  final override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = hashSeed
      result = 31 * result + ops.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null && javaClass == other.javaClass && ops == (other as MultiaryExpr<*, *>).ops)

  final override fun toString(): String =
    Utils.lispStringBuilder(operatorLabel).body().addAll(ops).toString()

  abstract fun with(ops: Iterable<Expr<OpType>>): MultiaryExpr<OpType, ExprType>

  protected abstract val hashSeed: Int

  abstract val operatorLabel: String
}
