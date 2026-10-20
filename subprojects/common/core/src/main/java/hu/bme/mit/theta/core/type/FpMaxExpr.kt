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
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.Serializable

@Serializable
class FpMaxExpr
private constructor(override val leftOp: Expr<FpType>, override val rightOp: Expr<FpType>) :
  BinaryExpr<FpType, FpType>() {

  init {
    checkAllTypesEqual(leftOp, rightOp)
  }

  override val type: FpType
    get() = leftOp.type

  override fun eval(valuation: Valuation): LitExpr<FpType> {
    val leftOpVal = leftOp.eval(valuation) as FpLitExpr
    val rightOpVal = rightOp.eval(valuation) as FpLitExpr
    return if (
      FpUtils.fpLitExprToBigFloat(null, leftOpVal)
        .greaterThan(FpUtils.fpLitExprToBigFloat(null, rightOpVal))
    )
      leftOpVal
    else rightOpVal
  }

  override fun with(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpMaxExpr =
    if (leftOp === this.leftOp && rightOp === this.rightOp) this else of(leftOp, rightOp)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 6668
    private const val OPERATOR_LABEL = "fpmax"

    @JvmStatic
    fun of(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpMaxExpr = FpMaxExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>): FpMaxExpr = of(castFp(leftOp), castFp(rightOp))
  }
}
