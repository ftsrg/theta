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

sealed class BinaryExpr<OpType : Type, ExprType : Type>
protected constructor(leftOp: Expr<OpType>, rightOp: Expr<OpType>) : AbstractExpr<ExprType>() {

  val leftOp: Expr<OpType> = checkNotNull(leftOp)
  val rightOp: Expr<OpType> = checkNotNull(rightOp)

  @Volatile private var hashCode = 0

  final override val arity: Int
    get() = 2

  final override val ops: List<Expr<OpType>>
    get() = ImmutableList.of(leftOp, rightOp)

  final override fun withOps(ops: List<Expr<*>>): BinaryExpr<OpType, ExprType> {
    checkArgument(ops.size == 2)
    val opType = leftOp.type
    val newLeftOp = TypeUtils.cast(ops[0], opType)
    val newRightOp = TypeUtils.cast(ops[1], opType)
    return with(newLeftOp, newRightOp)
  }

  final override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = hashSeed
      result = 31 * result + leftOp.hashCode()
      result = 31 * result + rightOp.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as BinaryExpr<*, *>
    return leftOp == that.leftOp && rightOp == that.rightOp
  }

  final override fun toString(): String =
    Utils.lispStringBuilder(operatorLabel).body().add(leftOp).add(rightOp).toString()

  abstract fun with(leftOp: Expr<OpType>, rightOp: Expr<OpType>): BinaryExpr<OpType, ExprType>

  open fun withLeftOp(leftOp: Expr<OpType>): BinaryExpr<OpType, ExprType> =
    with(leftOp, this.rightOp)

  open fun withRightOp(rightOp: Expr<OpType>): BinaryExpr<OpType, ExprType> =
    with(this.leftOp, rightOp)

  protected abstract val hashSeed: Int

  abstract val operatorLabel: String
}
