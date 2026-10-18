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
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual

class FpDivExpr
private constructor(
  val roundingMode: FpRoundingMode?,
  leftOp: Expr<FpType>,
  rightOp: Expr<FpType>,
) : DivExpr<FpType>(leftOp, rightOp) {

  init {
    checkAllTypesEqual(leftOp, rightOp)
  }

  override val type: FpType
    get() = leftOp.type

  override fun eval(valuation: Valuation): FpLitExpr {
    val leftOpVal = leftOp.eval(valuation) as FpLitExpr
    val rightOpVal = rightOp.eval(valuation) as FpLitExpr
    return leftOpVal.div(roundingMode, rightOpVal)
  }

  override fun with(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpDivExpr =
    if (leftOp === this.leftOp && rightOp === this.rightOp) this
    else keepSourceType(of(roundingMode, leftOp, rightOp))

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FpDivExpr
    return leftOp == that.leftOp && rightOp == that.rightOp && roundingMode == that.roundingMode
  }

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL + "[" + roundingMode!!.name.lowercase() + "]"

  companion object {
    private const val HASH_SEED = 1646
    private const val OPERATOR_LABEL = "fpdiv"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode?, leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpDivExpr =
      FpDivExpr(roundingMode, leftOp, rightOp)

    @JvmStatic
    fun create(roundingMode: FpRoundingMode?, leftOp: Expr<*>, rightOp: Expr<*>): FpDivExpr =
      of(roundingMode, castFp(leftOp), castFp(rightOp))
  }
}
