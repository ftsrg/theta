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
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.FpUtils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import org.kframework.mpfr.BigFloat

@Serializable
@SerialName("FpFromBv")
data class FpFromBvExpr(
  val roundingMode: FpRoundingMode,
  override val op: Expr<BvType>,
  val fpType: FpType,
  val signed: Boolean,
) : UnaryExpr<BvType, FpType>() {

  companion object {

    private const val OPERATOR_LABEL = "fpfrombv"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode, op: Expr<BvType>, fpType: FpType, signed: Boolean) =
      FpFromBvExpr(roundingMode, op, fpType, signed)

    @JvmStatic
    fun create(
      roundingMode: FpRoundingMode,
      op: Expr<BvType>,
      fpType: FpType,
      signed: Boolean,
    ): FpFromBvExpr = of(roundingMode, op, fpType, signed)
  }

  @Volatile @Transient private var hashCode = 0

  override val type: FpType
    get() = fpType

  fun isSigned(): Boolean = signed

  override fun eval(`val`: Valuation): FpLitExpr {
    val mathContext = FpUtils.getMathContext(fpType, roundingMode)
    val eval = op.eval(`val`) as BvLitExpr
    return FpUtils.bigFloatToFpLitExpr(
      BigFloat(
        if (signed) BvUtils.signedBvLitExprToBigInteger(eval)
        else BvUtils.unsignedBvLitExprToBigInteger(eval),
        mathContext,
      ),
      fpType,
    )
  }

  override fun new(op: Expr<BvType>): FpFromBvExpr = of(roundingMode, op, fpType, signed)

  override val operatorLabel: String =
    (OPERATOR_LABEL +
      "[" +
      fpType.exponent +
      "," +
      fpType.significand +
      "][" +
      (if (signed) "s" else "u") +
      "]")

  override fun toString(): String = super.toString()

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = op.hashCode()
      result = 31 * result + roundingMode.hashCode()
      result = 31 * result + fpType.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    if (this === other) {
      true
    } else if (other != null && this.javaClass == other.javaClass) {
      val that = other as FpFromBvExpr
      op == that.op && roundingMode == that.roundingMode && fpType == that.fpType
    } else {
      false
    }
}
