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
package hu.bme.mit.theta.core.type.bvtype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.utils.TypeUtils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("BvPos")
data class BvPosExpr(override val op: Expr<BvType>) : PosExpr<BvType>() {

  companion object {
    private const val OPERATOR_LABEL = "bvpos"

    @JvmStatic fun of(op: Expr<BvType>) = BvPosExpr(op)

    @JvmStatic fun create(op: Expr<*>) = BvPosExpr(TypeUtils.castBv(op))
  }

  override val type: BvType
    get() = op.type

  override fun eval(`val`: Valuation): BvLitExpr {
    val opVal = op.eval(`val`) as BvLitExpr
    return opVal.pos()
  }

  override fun new(op: Expr<BvType>): BvPosExpr = of(op)

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  override fun toString(): String = super.toString()
}
