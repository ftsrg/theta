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
package hu.bme.mit.theta.core.type.enumtype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("EnumEq")
data class EnumEqExpr(override val leftOp: Expr<EnumType>, override val rightOp: Expr<EnumType>) :
  EqExpr<EnumType>() {

  companion object {

    @JvmStatic fun of(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>) = EnumEqExpr(leftOp, rightOp)
  }

  override fun eval(`val`: Valuation): LitExpr<BoolType> =
    EnumLitExpr.eq(leftOp.eval(`val`) as EnumLitExpr, rightOp.eval(`val`) as EnumLitExpr)

  override fun new(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>): EnumEqExpr =
    of(leftOp, rightOp)

  override fun toString(): String = super.toString()
}
