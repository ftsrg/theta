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
package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Logical implication (=>) expression for boolean type. */
@Serializable
@SerialName("Imply")
data class ImplyExpr(override val leftOp: Expr<BoolType>, override val rightOp: Expr<BoolType>) :
  BinaryExpr<BoolType, BoolType>() {
  companion object {
    private const val OPERATOR_LABEL = "=>"

    @JvmStatic fun of(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = ImplyExpr(leftOp, rightOp)

    @JvmStatic
    fun create(leftOp: Expr<*>, rightOp: Expr<*>) =
      ImplyExpr(cast(leftOp, Bool()), cast(rightOp, Bool()))
  }

  override val type: BoolType = Bool()

  override fun eval(`val`: Valuation): BoolLitExpr =
    Bool(!(leftOp.eval(`val`) as BoolLitExpr).value || (rightOp.eval(`val`) as BoolLitExpr).value)

  override fun new(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): ImplyExpr =
    ImplyExpr(leftOp, rightOp)

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).add(leftOp).add(rightOp).toString()

  override val operatorLabel: String
    get() = OPERATOR_LABEL
}
