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
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.TypeUtils.castFp

class FpAbsExpr private constructor(op: Expr<FpType>) : UnaryExpr<FpType, FpType>(op) {

  override val type: FpType
    get() = op.type

  override fun eval(valuation: Valuation): FpLitExpr {
    val opVal = op.eval(valuation) as FpLitExpr
    return if (opVal.hidden) opVal.neg() else opVal
  }

  override fun with(op: Expr<FpType>): FpAbsExpr =
    if (op === this.op) this else keepSourceType(of(op))

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 6666
    private const val OPERATOR_LABEL = "fpabs"

    @JvmStatic fun of(op: Expr<FpType>): FpAbsExpr = FpAbsExpr(castFp(op))

    @JvmStatic fun create(op: Expr<*>): FpAbsExpr = of(castFp(op))
  }
}
