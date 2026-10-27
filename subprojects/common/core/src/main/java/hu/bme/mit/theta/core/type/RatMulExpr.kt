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

import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import java.math.BigInteger
import kotlinx.serialization.Serializable

@Serializable
class RatMulExpr private constructor(override val ops: List<Expr<RatType>>) : MulExpr<RatType>() {

  override val type: RatType
    get() = Rat()

  override fun eval(valuation: Valuation): RatLitExpr {
    var prodNum = BigInteger.ONE
    var prodDenom = BigInteger.ONE
    for (op in ops) {
      val opLit = op.eval(valuation) as RatLitExpr
      prodNum = prodNum.multiply(opLit.num)
      prodDenom = prodDenom.multiply(opLit.denom)
    }
    return Rat(prodNum, prodDenom)
  }

  override fun with(ops: Iterable<Expr<RatType>>): RatMulExpr =
    if (ops === this.ops) this else of(ops)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 9479
    private const val OPERATOR_LABEL = "*"

    @JvmStatic
    fun of(ops: Iterable<Expr<RatType>>): RatMulExpr = RatMulExpr(ImmutableList.copyOf(ops))

    @JvmStatic fun create(ops: List<Expr<*>>): RatMulExpr = of(ops.map { cast(it, Rat()) })
  }
}
