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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.Serializable

@Serializable
class FpIsInfiniteExpr private constructor(override val op: Expr<FpType>) :
  UnaryExpr<FpType, BoolType>() {

  init {
    checkAllTypesEqual(op)
  }

  override val type: BoolType
    get() = Bool()

  override fun eval(valuation: Valuation): BoolLitExpr {
    val opVal = op.eval(valuation) as FpLitExpr
    return Bool(opVal.isNegativeInfinity() || opVal.isPositiveInfinity())
  }

  override fun with(op: Expr<FpType>): FpIsInfiniteExpr = if (op === this.op) this else of(op)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 1756
    private const val OPERATOR_LABEL = "isinfinite"

    @JvmStatic fun of(op: Expr<FpType>): FpIsInfiniteExpr = FpIsInfiniteExpr(op)

    @JvmStatic fun create(op: Expr<*>): FpIsInfiniteExpr = of(castFp(op))
  }
}
