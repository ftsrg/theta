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
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual

class BvAndExpr private constructor(ops: Iterable<Expr<BvType>>) :
  MultiaryExpr<BvType, BvType>(ops) {

  init {
    checkAllTypesEqual(ops)
  }

  override val type: BvType
    get() = ops[0].type

  override fun eval(valuation: Valuation): BvLitExpr =
    ops.drop(1).fold(ops[0].eval(valuation) as BvLitExpr) { acc, op ->
      acc.and(op.eval(valuation) as BvLitExpr)
    }

  override fun with(ops: Iterable<Expr<BvType>>): BvAndExpr =
    if (ops === this.ops) this else keepSourceType(of(ops))

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 9125
    private const val OPERATOR_LABEL = "bvand"

    @JvmStatic fun of(ops: Iterable<Expr<BvType>>): BvAndExpr = BvAndExpr(ops)

    @JvmStatic fun create(ops: List<Expr<*>>): BvAndExpr = of(ops.map { castBv(it) })
  }
}
