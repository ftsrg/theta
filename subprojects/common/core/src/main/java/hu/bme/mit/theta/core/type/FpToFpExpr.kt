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
import hu.bme.mit.theta.core.utils.FpUtils

class FpToFpExpr
private constructor(
  val roundingMode: FpRoundingMode,
  op: Expr<FpType>,
  val expBits: Int,
  val signBits: Int,
) : UnaryExpr<FpType, FpType>(op) {

  override fun with(op: Expr<FpType>): FpToFpExpr =
    if (op === this.op) this else keepSourceType(of(roundingMode, op, expBits, signBits))

  override val type: FpType
    get() = FpType.of(expBits, signBits)

  override fun eval(valuation: Valuation): FpLitExpr {
    val op = op.eval(valuation) as FpLitExpr
    val value = FpUtils.fpLitExprToBigFloat(roundingMode, op)
    return FpUtils.bigFloatToFpLitExpr(value, type)
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FpToFpExpr
    return op == that.op &&
      expBits == that.expBits &&
      signBits == that.signBits &&
      roundingMode == that.roundingMode
  }

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = "$OPERATOR_LABEL[$expBits,$signBits]"

  companion object {
    private const val HASH_SEED = 6799
    private const val OPERATOR_LABEL = "fptofp"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode, op: Expr<FpType>, exp: Int, signBits: Int): FpToFpExpr =
      FpToFpExpr(roundingMode, op, exp, signBits)

    @JvmStatic
    fun create(
      roundingMode: FpRoundingMode,
      op: Expr<FpType>,
      exp: Int,
      signBits: Int,
    ): FpToFpExpr = of(roundingMode, op, exp, signBits)
  }
}
