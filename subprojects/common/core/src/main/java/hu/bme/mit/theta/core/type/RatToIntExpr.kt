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
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.TypeUtils.cast

class RatToIntExpr private constructor(op: Expr<RatType>) : UnaryExpr<RatType, IntType>(op) {

  override val type: IntType
    get() = Int()

  override fun eval(valuation: Valuation): IntLitExpr = (op.eval(valuation) as RatLitExpr).toInt()

  override fun with(op: Expr<RatType>): RatToIntExpr =
    if (op === this.op) this else keepSourceType(of(op))

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 4828
    private const val OPERATOR_LABEL = "to_int"

    @JvmStatic fun of(op: Expr<RatType>): RatToIntExpr = RatToIntExpr(op)

    @JvmStatic fun create(op: Expr<*>): RatToIntExpr = of(cast(op, Rat()))
  }
}
