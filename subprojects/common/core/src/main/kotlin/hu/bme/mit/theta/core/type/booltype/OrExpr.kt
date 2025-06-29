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
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Logical OR expression for boolean type. */
@Serializable
@SerialName("Or")
data class OrExpr(override val ops: List<Expr<BoolType>>) : MultiaryExpr<BoolType, BoolType>() {

  companion object {

    private const val OPERATOR_LABEL = "or"

    @JvmStatic fun of(ops: Iterable<Expr<BoolType>>) = OrExpr(ops.toList())

    @JvmStatic fun create(ops: List<Expr<*>>) = OrExpr(ops.map { cast(it, Bool()) })
  }

  override val type: BoolType = Bool()

  override fun eval(`val`: Valuation): BoolLitExpr =
    if (ops.any { (it.eval(`val`) as BoolLitExpr).value }) True() else False()

  override fun new(ops: List<Expr<BoolType>>): OrExpr = of(ops)

  override fun toString(): String = super.toString()

  override val operatorLabel: String
    get() = OPERATOR_LABEL
}
