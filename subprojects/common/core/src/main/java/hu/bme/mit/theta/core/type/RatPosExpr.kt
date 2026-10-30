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
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

@Serializable
class RatPosExpr private constructor(override val op: Expr<RatType>) : PosExpr<RatType>() {

  override val type: RatType
    get() = Rat()

  override fun eval(valuation: Valuation): RatLitExpr = (op.eval(valuation) as RatLitExpr).pos()

  override fun with(op: Expr<RatType>): RatPosExpr = if (op === this.op) this else of(op)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 4827
    private const val OPERATOR_LABEL = "+"

    @JvmStatic fun of(op: Expr<RatType>): RatPosExpr = RatPosExpr(op)

    @JvmStatic fun create(op: Expr<*>): RatPosExpr = of(cast(op, Rat()))
  }
}
