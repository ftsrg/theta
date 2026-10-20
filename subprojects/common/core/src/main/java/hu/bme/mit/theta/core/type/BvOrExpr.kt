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
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.utils.TypeUtils.castBv
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.Serializable

@Serializable
class BvOrExpr private constructor(override val ops: List<Expr<BvType>>) :
  MultiaryExpr<BvType, BvType>() {

  init {
    checkAllTypesEqual(ops)
  }

  override val type: BvType
    get() = ops[0].type

  override fun eval(valuation: Valuation): BvLitExpr =
    ops.drop(1).fold(ops[0].eval(valuation) as BvLitExpr) { acc, op ->
      acc.or(op.eval(valuation) as BvLitExpr)
    }

  override fun with(ops: Iterable<Expr<BvType>>): BvOrExpr = if (ops === this.ops) this else of(ops)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 2745
    private const val OPERATOR_LABEL = "bvor"

    @JvmStatic fun of(ops: Iterable<Expr<BvType>>): BvOrExpr = BvOrExpr(ImmutableList.copyOf(ops))

    @JvmStatic fun create(ops: List<Expr<*>>): BvOrExpr = of(ops.map { castBv(it) })
  }
}
