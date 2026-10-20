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
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.utils.TypeUtils.castBv
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.Serializable

@Serializable
class BvRotateRightExpr
private constructor(override val leftOp: Expr<BvType>, override val rightOp: Expr<BvType>) :
  BinaryExpr<BvType, BvType>() {

  init {
    checkAllTypesEqual(leftOp, rightOp)
  }

  override val type: BvType
    get() = leftOp.type

  override fun eval(valuation: Valuation): BvLitExpr {
    val leftOpVal = leftOp.eval(valuation) as BvLitExpr
    val rightOpVal = rightOp.eval(valuation) as BvLitExpr
    return leftOpVal.rotateRight(rightOpVal)
  }

  override fun with(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvRotateRightExpr =
    if (leftOp === this.leftOp && rightOp === this.rightOp) this else of(leftOp, rightOp)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 2564
    private const val OPERATOR_LABEL = "bvror"

    @JvmStatic
    fun of(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvRotateRightExpr =
      BvRotateRightExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>): BvRotateRightExpr =
      of(castBv(leftOp), castBv(rightOp))
  }
}
