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
package hu.bme.mit.theta.core.type.rattype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.DivExpr
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("RatDiv")
data class RatDivExpr(override val leftOp: Expr<RatType>, override val rightOp: Expr<RatType>) :
  DivExpr<RatType>() {

  companion object {
    private const val OPERATOR_LABEL = "/"

    @JvmStatic fun of(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatDivExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>): RatDivExpr {
      val newLeftOp =
        when (leftOp.type) {
          is RatType -> cast(leftOp, Rat())
          is IntType -> IntToRatExpr.create(leftOp)
          else -> throw IllegalArgumentException("Unsupported type for RatDiv: ${leftOp.type}")
        }
      val newRightOp =
        when (rightOp.type) {
          is RatType -> cast(rightOp, Rat())
          is IntType -> IntToRatExpr.create(rightOp)
          else -> throw IllegalArgumentException("Unsupported type for RatDiv: ${rightOp.type}")
        }
      return RatDivExpr(newLeftOp, newRightOp)
    }
  }

  override val type: RatType = Rat()

  override fun eval(`val`: Valuation): RatLitExpr {
    val leftOpVal = leftOp.eval(`val`) as RatLitExpr
    val rightOpVal = rightOp.eval(`val`) as RatLitExpr
    return leftOpVal.div(rightOpVal)
  }

  override fun new(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatDivExpr = of(leftOp, rightOp)

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  override fun toString(): String = super.toString()
}
