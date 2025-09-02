/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.type.fptype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.castFp
import hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpIsNan")
data class FpIsNanExpr(override val op: Expr<FpType>) : UnaryExpr<FpType, BoolType>() {

  init {
    checkAllTypesEqual(op)
  }

  companion object {
    private const val OPERATOR_LABEL = "fpisnan"

    @JvmStatic fun of(op: Expr<FpType>) = FpIsNanExpr(op)

    @JvmStatic fun create(op: Expr<*>) = FpIsNanExpr(castFp(op))
  }

  override val type: BoolType
    get() = Bool()

  override fun eval(`val`: Valuation): BoolLitExpr = Bool((op.eval(`val`) as FpLitExpr).isNaN())

  override fun new(op: Expr<FpType>): FpIsNanExpr = of(op)

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  override fun toString(): String = super.toString()
}
