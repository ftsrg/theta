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

import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import kotlinx.serialization.Serializable

@Serializable
class FpFromIeeeBvExpr private constructor(override val op: Expr<BvType>, val fpType: FpType) :
  UnaryExpr<BvType, FpType>() {

  override val type: FpType
    get() = fpType

  override fun eval(valuation: Valuation): FpLitExpr {
    val op = op.eval(valuation) as BvLitExpr
    // Decompose sign ++ exponent ++ fraction with the *stored* widths -- the fraction is
    // getSignificand() - 1 bits, the implicit leading bit not being encoded. FpLitExpr.of(bv,
    // fpType) uses a different convention and would misread this, so slice it out by hand,
    // the exact inverse of FpToIeeeBvExpr#eval.
    val bits = op.value
    val exp = fpType.exponent
    val fraction = fpType.significand - 1
    val exponent = bits.copyOfRange(1, 1 + exp)
    val significand = bits.copyOfRange(1 + exp, 1 + exp + fraction)
    return FpLitExpr.of(
      BvLitExpr.of(booleanArrayOf(bits[0])),
      BvLitExpr.of(exponent),
      BvLitExpr.of(significand),
    )
  }

  override fun with(op: Expr<BvType>): FpFromIeeeBvExpr =
    if (op === this.op) this else of(op, fpType)

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FpFromIeeeBvExpr
    return op == that.op && fpType == that.fpType
  }

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL + "[" + fpType.exponent + "," + fpType.significand + "]"

  companion object {
    private const val HASH_SEED = 6829
    private const val OPERATOR_LABEL = "fpfromieeebv"

    @JvmStatic
    fun of(op: Expr<BvType>, fpType: FpType): FpFromIeeeBvExpr {
      checkArgument(
        op.type.size == FpToIeeeBvExpr.bitWidth(fpType),
        "The bitvector width must equal the float's encoded width",
      )
      return FpFromIeeeBvExpr(op, fpType)
    }

    @JvmStatic fun create(op: Expr<BvType>, fpType: FpType): FpFromIeeeBvExpr = of(op, fpType)
  }
}
