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
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.utils.FpUtils.bigFloatToFpLitExpr
import hu.bme.mit.theta.core.utils.FpUtils.fpLitExprToBigFloat
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpToFp")
data class FpToFpExpr(
  val roundingMode: FpRoundingMode,
  override val op: Expr<FpType>,
  val expBits: Int,
  val signBits: Int,
) : UnaryExpr<FpType, FpType>() {

  companion object {
    private const val OPERATOR_LABEL = "fptofp"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode, op: Expr<FpType>, expBits: Int, signBits: Int) =
      FpToFpExpr(roundingMode, op, expBits, signBits)

    @JvmStatic
    fun create(roundingMode: FpRoundingMode, op: Expr<*>, expBits: Int, signBits: Int) =
      FpToFpExpr(roundingMode, castFp(op), expBits, signBits)
  }

  override val type: FpType
    get() = FpType(expBits, signBits)

  override fun eval(`val`: Valuation): FpLitExpr {
    val op = op.eval(`val`) as FpLitExpr
    val value = fpLitExprToBigFloat(roundingMode, op)
    return bigFloatToFpLitExpr(value, type)
  }

  override fun new(op: Expr<FpType>): FpToFpExpr = of(roundingMode, op, expBits, signBits)

  override val operatorLabel: String = "$OPERATOR_LABEL[$expBits,$signBits]"

  override fun toString(): String = super.toString()
}
