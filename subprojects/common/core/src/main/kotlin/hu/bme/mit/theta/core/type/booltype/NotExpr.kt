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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Logical NOT expression for boolean type. */
@Serializable
@SerialName("Not")
data class NotExpr(override val op: Expr<BoolType>) : UnaryExpr<BoolType, BoolType>() {

  companion object {

    private const val OPERATOR_LABEL = "not"

    @JvmStatic fun of(op: Expr<BoolType>) = NotExpr(op)

    @JvmStatic fun create(op: Expr<*>) = NotExpr(cast(op, Bool()))
  }

  override val type: BoolType = Bool()

  override fun eval(`val`: Valuation): BoolLitExpr = Bool(!(op.eval(`val`) as BoolLitExpr).value)

  override fun new(op: Expr<BoolType>): NotExpr = NotExpr(op)

  override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL).add(op).toString()

  override val operatorLabel: String = OPERATOR_LABEL
}
