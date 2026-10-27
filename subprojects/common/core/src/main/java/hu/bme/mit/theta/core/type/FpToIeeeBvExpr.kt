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
import hu.bme.mit.theta.core.type.fptype.FpType
import kotlinx.serialization.Serializable

@Serializable
class FpToIeeeBvExpr private constructor(override val op: Expr<FpType>) :
  UnaryExpr<FpType, BvType>() {

  override val type: BvType
    get() = BvType.of(bitWidth(op.type))

  override fun eval(valuation: Valuation): BvLitExpr {
    val op = op.eval(valuation) as FpLitExpr
    // sign ++ exponent ++ significand -- exactly the order FpLitExpr.of(bv, fpType) reads back.
    val exponent = op.exponent.value
    val significand = op.significand.value
    val bits = BooleanArray(1 + exponent.size + significand.size)
    bits[0] = op.hidden
    exponent.copyInto(bits, 1)
    significand.copyInto(bits, 1 + exponent.size)
    return BvLitExpr.of(bits)
  }

  override fun with(op: Expr<FpType>): FpToIeeeBvExpr = if (op === this.op) this else of(op)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 6817
    private const val OPERATOR_LABEL = "fptoieeebv"

    @JvmStatic fun of(op: Expr<FpType>): FpToIeeeBvExpr = FpToIeeeBvExpr(op)

    @JvmStatic fun create(op: Expr<FpType>): FpToIeeeBvExpr = of(op)

    /**
     * The bitvector width the float's format encodes to.
     *
     * `getSignificand()` counts the implicit leading bit, which IEEE does not store, so the
     * on-the-wire fraction is `getSignificand() - 1` bits. With the sign bit the total is `1 +
     * exponent + (significand - 1) == exponent + significand`: 64 for double `FpType.of(11, 53)`,
     * 32 for float `FpType.of(8, 24)`. (Not `+ 1` more -- `FpLitExpr.of(bv, fpType)` uses a
     * different, incompatible convention; do not route through it.)
     */
    @JvmStatic fun bitWidth(fpType: FpType): Int = fpType.exponent + fpType.significand
  }
}
