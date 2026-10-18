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
import com.google.common.base.Preconditions.checkNotNull
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.utils.TypeUtils

sealed class UnaryExpr<OpType : Type, ExprType : Type>(op: Expr<OpType>) :
  AbstractExpr<ExprType>() {

  val op: Expr<OpType> = checkNotNull(op)

  @Volatile private var hashCode = 0

  final override val ops: List<Expr<OpType>>
    get() = ImmutableList.of(op)

  final override fun withOps(ops: List<Expr<*>>): UnaryExpr<OpType, ExprType> {
    checkArgument(ops.size == 1)
    val opType = op.type
    val newOp = TypeUtils.cast(ops[0], opType)
    return with(newOp)
  }

  override val arity: Int
    get() = 1

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = hashSeed
      result = 37 * result + op.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null && javaClass == other.javaClass && op == (other as UnaryExpr<*, *>).op)

  final override fun toString(): String =
    Utils.lispStringBuilder(operatorLabel).body().add(op).toString()

  abstract fun with(op: Expr<OpType>): UnaryExpr<OpType, ExprType>

  protected abstract val hashSeed: Int

  abstract val operatorLabel: String
}
