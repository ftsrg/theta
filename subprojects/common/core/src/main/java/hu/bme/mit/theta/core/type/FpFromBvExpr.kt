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
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.FpUtils
import org.kframework.mpfr.BigFloat

class FpFromBvExpr
private constructor(
  val roundingMode: FpRoundingMode,
  op: Expr<BvType>,
  val fpType: FpType,
  val isSigned: Boolean,
) : UnaryExpr<BvType, FpType>(op) {

  override val type: FpType
    get() = fpType

  override fun eval(valuation: Valuation): FpLitExpr {
    val mathContext = FpUtils.getMathContext(fpType, roundingMode)
    val eval = op.eval(valuation) as BvLitExpr
    val value =
      if (isSigned) BvUtils.signedBvLitExprToBigInteger(eval)
      else BvUtils.unsignedBvLitExprToBigInteger(eval)
    return FpUtils.bigFloatToFpLitExpr(BigFloat(value, mathContext), fpType)
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FpFromBvExpr
    return op == that.op && fpType == that.fpType && roundingMode == that.roundingMode
  }

  override fun with(op: Expr<BvType>): FpFromBvExpr =
    keepSourceType(FpFromBvExpr(roundingMode, op, fpType, isSigned))

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() =
      OPERATOR_LABEL +
        "[" +
        fpType.exponent +
        "," +
        fpType.significand +
        "][" +
        (if (isSigned) "s" else "u") +
        "]"

  companion object {
    private const val HASH_SEED = 6696
    private const val OPERATOR_LABEL = "fpfrombv"

    @JvmStatic
    fun of(
      roundingMode: FpRoundingMode,
      op: Expr<BvType>,
      fpType: FpType,
      signed: Boolean,
    ): FpFromBvExpr = FpFromBvExpr(roundingMode, op, fpType, signed)

    @JvmStatic
    fun create(
      roundingMode: FpRoundingMode,
      op: Expr<BvType>,
      fpType: FpType,
      signed: Boolean,
    ): FpFromBvExpr = of(roundingMode, op, fpType, signed)
  }
}
