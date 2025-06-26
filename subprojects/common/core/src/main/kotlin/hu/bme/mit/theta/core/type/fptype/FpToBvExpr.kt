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
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToSignedBvLitExpr
import hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToUnsignedBvLitExpr
import hu.bme.mit.theta.core.utils.FpUtils.fpLitExprToBigFloat
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpToBv")
data class FpToBvExpr(
  val roundingMode: FpRoundingMode,
  override val op: Expr<FpType>,
  val size: Int,
  val sgn: Boolean,
) : UnaryExpr<FpType, BvType>() {

  companion object {

    private const val OPERATOR_LABEL = "fptobv"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode, op: Expr<FpType>, size: Int, sgn: Boolean) =
      FpToBvExpr(roundingMode, op, size, sgn)

    @JvmStatic
    fun create(roundingMode: FpRoundingMode, op: Expr<*>, size: Int, sgn: Boolean) =
      FpToBvExpr(roundingMode, castFp(op), size, sgn)
  }

  override val type: BvType
    get() = BvType.of(size)

  override fun eval(`val`: Valuation): BvLitExpr {
    val op = op.eval(`val`) as FpLitExpr
    val bigIntegerValue = fpLitExprToBigFloat(roundingMode, op).toBigInteger()
    return if (sgn) {
      bigIntegerToSignedBvLitExpr(bigIntegerValue, size)
    } else {
      bigIntegerToUnsignedBvLitExpr(bigIntegerValue, size)
    }
  }

  override fun new(op: Expr<FpType>): FpToBvExpr = of(roundingMode, op, size, sgn)

  override val operatorLabel: String =
    (OPERATOR_LABEL +
      "[" +
      "[" +
      size +
      "'" +
      (if (sgn) "s" else "u") +
      "][" +
      roundingMode.name +
      "]")

  override fun toString(): String = super.toString()
}
