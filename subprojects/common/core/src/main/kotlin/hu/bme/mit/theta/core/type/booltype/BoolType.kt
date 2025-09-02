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

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Boolean type for expressions. */
@Serializable
@SerialName(BoolType.TYPE_LABEL)
data object BoolType : Equational<BoolType> {

  internal const val TYPE_LABEL = "Bool"

  @JvmStatic fun getInstance(): BoolType = this

  override fun toString(): String = TYPE_LABEL

  override fun Eq(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): IffExpr =
    BoolExprs.Iff(leftOp, rightOp)

  override fun Neq(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): NeqExpr<BoolType> =
    BoolExprs.Xor(leftOp, rightOp)

  override val domainSize: DomainSize = DomainSize.TWO
}
