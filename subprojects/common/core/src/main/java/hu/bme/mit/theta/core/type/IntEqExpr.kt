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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

@Serializable
class IntEqExpr
private constructor(override val leftOp: Expr<IntType>, override val rightOp: Expr<IntType>) :
  EqExpr<IntType>() {

  override val type: BoolType
    get() = Bool()

  override fun eval(valuation: Valuation): BoolLitExpr {
    val leftOpVal = leftOp.eval(valuation) as IntLitExpr
    val rightOpVal = rightOp.eval(valuation) as IntLitExpr
    return leftOpVal.eq(rightOpVal)
  }

  override fun with(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntEqExpr =
    if (leftOp === this.leftOp && rightOp === this.rightOp) this else of(leftOp, rightOp)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 2777
    private const val OPERATOR_LABEL = "="

    @JvmStatic
    fun of(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntEqExpr = IntEqExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>): IntEqExpr =
      of(cast(leftOp, Int()), cast(rightOp, Int()))
  }
}
