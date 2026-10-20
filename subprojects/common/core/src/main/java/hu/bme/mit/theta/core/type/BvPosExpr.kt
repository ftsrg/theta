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
import hu.bme.mit.theta.core.utils.TypeUtils.castBv
import kotlinx.serialization.Serializable

@Serializable
class BvPosExpr private constructor(override val op: Expr<BvType>) : PosExpr<BvType>() {

  override val type: BvType
    get() = op.type

  override fun eval(valuation: Valuation): BvLitExpr = (op.eval(valuation) as BvLitExpr).pos()

  override fun with(op: Expr<BvType>): BvPosExpr = if (op === this.op) this else of(op)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 8962
    private const val OPERATOR_LABEL = "bvpos"

    @JvmStatic fun of(op: Expr<BvType>): BvPosExpr = BvPosExpr(op)

    @JvmStatic fun create(op: Expr<*>): BvPosExpr = of(castBv(op))
  }
}
