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
package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.core.type.Expr

/** Utility methods for smart construction and simplification of boolean expressions. */
@Suppress("FunctionName")
object SmartBoolExprs {

  @JvmStatic
  fun Not(op: Expr<BoolType>): Expr<BoolType> =
    when (op) {
      BoolExprs.True() -> BoolExprs.False()
      BoolExprs.False() -> BoolExprs.True()
      is NotExpr -> op.op
      else -> BoolExprs.Not(op)
    }

  @JvmStatic
  fun Imply(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): Expr<BoolType> =
    when {
      leftOp == BoolExprs.False() -> BoolExprs.True()
      leftOp == BoolExprs.True() -> rightOp
      rightOp == BoolExprs.False() -> Not(leftOp)
      rightOp == BoolExprs.True() -> BoolExprs.True()
      else -> BoolExprs.Imply(leftOp, rightOp)
    }

  @JvmStatic
  fun And(ops: Collection<Expr<BoolType>>): Expr<BoolType> {
    if (ops.isEmpty()) return BoolExprs.True()
    if (BoolExprs.False() in ops) return BoolExprs.False()
    val filteredOps = ops.filter { it != BoolExprs.True() }
    return when (filteredOps.size) {
      0 -> BoolExprs.True()
      1 -> filteredOps.single()
      else -> BoolExprs.And(filteredOps)
    }
  }

  @JvmStatic
  fun Or(ops: Collection<Expr<BoolType>>): Expr<BoolType> {
    if (ops.isEmpty()) return BoolExprs.False()
    if (BoolExprs.True() in ops) return BoolExprs.True()
    val filteredOps = ops.filter { it != BoolExprs.False() }
    return when (filteredOps.size) {
      0 -> BoolExprs.False()
      1 -> filteredOps.single()
      else -> BoolExprs.Or(filteredOps)
    }
  }

  // Convenience methods
  @JvmStatic fun And(vararg ops: Expr<BoolType>) = And(ops.toList())

  @JvmStatic fun Or(vararg ops: Expr<BoolType>) = Or(ops.toList())
}
