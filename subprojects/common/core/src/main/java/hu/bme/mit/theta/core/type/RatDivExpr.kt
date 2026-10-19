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
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.TypeUtils.cast

class RatDivExpr private constructor(leftOp: Expr<RatType>, rightOp: Expr<RatType>) :
  DivExpr<RatType>(leftOp, rightOp) {

  override val type: RatType
    get() = Rat()

  override fun eval(valuation: Valuation): RatLitExpr {
    val leftOpVal = leftOp.eval(valuation) as RatLitExpr
    val rightOpVal = rightOp.eval(valuation) as RatLitExpr
    return leftOpVal.div(rightOpVal)
  }

  override fun with(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatDivExpr =
    if (leftOp === this.leftOp && rightOp === this.rightOp) this
    else keepSourceType(of(leftOp, rightOp))

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 139
    private const val OPERATOR_LABEL = "/"

    @JvmStatic
    fun of(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatDivExpr = RatDivExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>): RatDivExpr =
      of(toRat(leftOp, leftOp), toRat(rightOp, leftOp))

    // Reports the left operand's type on failure for either side.
    private fun toRat(op: Expr<*>, reported: Expr<*>): Expr<RatType> =
      when (op.type) {
        is RatType -> cast(op, Rat())
        is IntType -> IntToRatExpr.create(op)
        else -> throw IllegalArgumentException("Unsupported type for RatDiv: " + reported.type)
      }
  }
}
