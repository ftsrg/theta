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
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual

class FpAddExpr private constructor(val roundingMode: FpRoundingMode, ops: Iterable<Expr<FpType>>) :
  AddExpr<FpType>(ops) {

  init {
    checkAllTypesEqual(ops)
  }

  override val type: FpType
    get() = ops[0].type

  override fun eval(valuation: Valuation): FpLitExpr =
    ops.drop(1).fold(ops[0].eval(valuation) as FpLitExpr) { acc, op ->
      acc.add(roundingMode, op.eval(valuation) as FpLitExpr)
    }

  override fun with(ops: Iterable<Expr<FpType>>): FpAddExpr =
    if (ops === this.ops) this else keepSourceType(of(roundingMode, ops))

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FpAddExpr
    return ops == that.ops && roundingMode == that.roundingMode
  }

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 6588
    private const val OPERATOR_LABEL = "fpadd"

    @JvmStatic
    fun of(roundingMode: FpRoundingMode, ops: Iterable<Expr<FpType>>): FpAddExpr =
      FpAddExpr(roundingMode, ops)

    @JvmStatic
    fun create(roundingMode: FpRoundingMode, ops: List<Expr<*>>): FpAddExpr =
      of(roundingMode, ops.map { castFp(it) })
  }
}
