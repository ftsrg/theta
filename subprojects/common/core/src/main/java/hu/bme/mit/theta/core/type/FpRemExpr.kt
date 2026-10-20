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
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.Serializable

@Serializable
class FpRemExpr
private constructor(override val leftOp: Expr<FpType>, override val rightOp: Expr<FpType>) :
  BinaryExpr<FpType, FpType>() {

  init {
    checkAllTypesEqual(leftOp, rightOp)
  }

  override val type: FpType
    get() = leftOp.type

  override fun eval(valuation: Valuation): FpLitExpr {
    val leftFloat = FpUtils.fpLitExprToBigFloat(null, leftOp.eval(valuation) as FpLitExpr)
    val rightFloat = FpUtils.fpLitExprToBigFloat(null, rightOp.eval(valuation) as FpLitExpr)
    val remainder = leftFloat.remainder(rightFloat, FpUtils.getMathContext(type, null))
    return FpUtils.bigFloatToFpLitExpr(remainder, type)
  }

  override fun with(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpRemExpr =
    if (leftOp === this.leftOp && rightOp === this.rightOp) this else of(leftOp, rightOp)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 6670
    private const val OPERATOR_LABEL = "fprem"

    @JvmStatic
    fun of(leftOp: Expr<FpType>, rightOp: Expr<FpType>): FpRemExpr = FpRemExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>): FpRemExpr = of(castFp(leftOp), castFp(rightOp))
  }
}
