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
import kotlinx.serialization.Serializable

@Serializable
class FpToBvExpr
private constructor(
  val roundingMode: FpRoundingMode,
  override val op: Expr<FpType>,
  val size: Int,
  val sgn: Boolean,
) : UnaryExpr<FpType, BvType>() {

  override fun with(op: Expr<FpType>): FpToBvExpr =
    if (op === this.op) this else of(roundingMode, op, size, sgn)

  override val type: BvType
    get() = BvType.of(size)

  override fun eval(valuation: Valuation): BvLitExpr {
    val op = op.eval(valuation) as FpLitExpr
    val bigIntegerValue = FpUtils.round(FpUtils.fpLitExprToBigFloat(roundingMode, op), roundingMode)
    return if (sgn) BvUtils.bigIntegerToSignedBvLitExpr(bigIntegerValue, size)
    else BvUtils.bigIntegerToUnsignedBvLitExpr(bigIntegerValue, size)
  }

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FpToBvExpr
    return op == that.op &&
      size == that.size &&
      sgn == that.sgn &&
      roundingMode == that.roundingMode
  }

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() =
      OPERATOR_LABEL + "[" + size + "'" + (if (sgn) "s" else "u") + "][" + roundingMode.name + "]"

  companion object {
    private const val HASH_SEED = 6796
    private const val OPERATOR_LABEL = "fptobv"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode, op: Expr<FpType>, size: Int, sgn: Boolean): FpToBvExpr =
      FpToBvExpr(roundingMode, op, size, sgn)

    @JvmStatic
    fun create(
      roundingMode: FpRoundingMode,
      op: Expr<FpType>,
      size: Int,
      sgn: Boolean,
    ): FpToBvExpr = of(roundingMode, op, size, sgn)
  }
}
