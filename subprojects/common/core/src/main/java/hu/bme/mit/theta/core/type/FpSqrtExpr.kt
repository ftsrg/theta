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
import hu.bme.mit.theta.core.utils.TypeUtils.castFp

class FpSqrtExpr private constructor(val roundingMode: FpRoundingMode, op: Expr<FpType>) :
  UnaryExpr<FpType, FpType>(op) {

  override val type: FpType
    get() = op.type

  override fun eval(valuation: Valuation): LitExpr<FpType> {
    val opVal = op.eval(valuation) as FpLitExpr
    val sqrt =
      FpUtils.fpLitExprToBigFloat(roundingMode, opVal)
        .sqrt(FpUtils.getMathContext(type, roundingMode))
    return FpUtils.bigFloatToFpLitExpr(sqrt, type)
  }

  override fun with(op: Expr<FpType>): FpSqrtExpr =
    if (op === this.op) this else keepSourceType(of(roundingMode, op))

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FpSqrtExpr
    return op == that.op && roundingMode == that.roundingMode
  }

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 6669
    private const val OPERATOR_LABEL = "fpsqrt"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode, op: Expr<FpType>): FpSqrtExpr =
      FpSqrtExpr(roundingMode, castFp(op))

    @JvmStatic
    fun create(roundingMode: FpRoundingMode, op: Expr<*>): FpSqrtExpr = of(roundingMode, castFp(op))
  }
}
