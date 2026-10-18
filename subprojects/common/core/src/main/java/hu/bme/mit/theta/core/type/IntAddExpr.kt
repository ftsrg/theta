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
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import java.math.BigInteger

class IntAddExpr private constructor(ops: Iterable<Expr<IntType>>) : AddExpr<IntType>(ops) {

  override val type: IntType
    get() = Int()

  override fun eval(valuation: Valuation): IntLitExpr {
    var sum = BigInteger.ZERO
    for (op in ops) {
      sum = sum.add((op.eval(valuation) as IntLitExpr).value)
    }
    return Int(sum)
  }

  override fun with(ops: Iterable<Expr<IntType>>): IntAddExpr =
    if (ops === this.ops) this else keepSourceType(of(ops))

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 5653
    private const val OPERATOR_LABEL = "+"

    @JvmStatic fun of(ops: Iterable<Expr<IntType>>): IntAddExpr = IntAddExpr(ops)

    @JvmStatic fun create(ops: List<Expr<*>>): IntAddExpr = of(ops.map { cast(it, Int()) })
  }
}
