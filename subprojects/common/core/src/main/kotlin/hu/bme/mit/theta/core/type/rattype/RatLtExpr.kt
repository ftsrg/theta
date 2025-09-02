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
import hu.bme.mit.theta.core.type.abstracttype.LtExpr
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("RatLt")
data class RatLtExpr(override val leftOp: Expr<RatType>, override val rightOp: Expr<RatType>) :
  LtExpr<RatType>() {

  companion object {

    @JvmStatic fun of(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatLtExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>) =
      RatLtExpr(cast(leftOp, Rat()), cast(rightOp, Rat()))
  }

  override fun eval(`val`: Valuation): BoolLitExpr {
    val leftOpVal = leftOp.eval(`val`) as RatLitExpr
    val rightOpVal = rightOp.eval(`val`) as RatLitExpr
    return leftOpVal.lt(rightOpVal)
  }

  override fun new(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatLtExpr = of(leftOp, rightOp)

  override fun toString(): String = super.toString()
}
