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
package hu.bme.mit.theta.core.type.fptype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.DivExpr
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpDiv")
data class FpDivExpr(
  val roundingMode: FpRoundingMode,
  override val leftOp: Expr<FpType>,
  override val rightOp: Expr<FpType>,
) : DivExpr<FpType>() {

  init {
    checkAllTypesEqual(leftOp, rightOp)
  }

  companion object {
    private const val OPERATOR_LABEL = "fpdiv"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode, leftOp: Expr<FpType>, rightOp: Expr<FpType>) =
      FpDivExpr(roundingMode, leftOp, rightOp)

    @JvmStatic
    fun create(roundingMode: FpRoundingMode, leftOp: Expr<*>, rightOp: Expr<*>) =
      FpDivExpr(roundingMode, castFp(leftOp), castFp(rightOp))
  }

  override val type: FpType
    get() = leftOp.type

  override fun eval(`val`: Valuation): FpLitExpr {
    val leftOpVal = leftOp.eval(`val`) as FpLitExpr
    val rightOpVal = rightOp.eval(`val`) as FpLitExpr
    return leftOpVal.div(roundingMode, rightOpVal)
  }

  override fun new(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpDivExpr =
    of(roundingMode, leftOp, rightOp)

  override val operatorLabel: String
    get() = "$OPERATOR_LABEL[${roundingMode.name.lowercase()}]"

  override fun toString(): String = super.toString()
}
