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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

@Serializable
class AndExpr private constructor(override val ops: List<Expr<BoolType>>) :
  MultiaryExpr<BoolType, BoolType>() {

  override val type: BoolType
    get() = Bool()

  override fun eval(valuation: Valuation): BoolLitExpr {
    for (op in ops) {
      if (!(op.eval(valuation) as BoolLitExpr).value) return False()
    }
    return True()
  }

  override fun with(ops: Iterable<Expr<BoolType>>): AndExpr =
    if (ops === this.ops) this else of(ops)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 41
    private const val OPERATOR_LABEL = "and"

    @JvmStatic fun of(ops: Iterable<Expr<BoolType>>): AndExpr = AndExpr(ImmutableList.copyOf(ops))

    @JvmStatic fun create(ops: List<Expr<*>>): AndExpr = of(ops.map { cast(it, Bool()) })
  }
}
