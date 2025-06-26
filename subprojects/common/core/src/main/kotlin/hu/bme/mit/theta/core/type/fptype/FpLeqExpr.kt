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
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpLeq")
data class FpLeqExpr(override val leftOp: Expr<FpType>, override val rightOp: Expr<FpType>) :
  LeqExpr<FpType>() {
  init {
    checkAllTypesEqual(leftOp, rightOp)
  }

  companion object {
    @JvmStatic fun of(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpLeqExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>) = FpLeqExpr(castFp(leftOp), castFp(rightOp))
  }

  override fun eval(`val`: Valuation): BoolLitExpr {
    val leftOpVal = leftOp.eval(`val`) as FpLitExpr
    val rightOpVal = rightOp.eval(`val`) as FpLitExpr
    return leftOpVal.leq(rightOpVal)
  }

  override fun new(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpLeqExpr = of(leftOp, rightOp)

  override fun toString(): String = super.toString()
}
