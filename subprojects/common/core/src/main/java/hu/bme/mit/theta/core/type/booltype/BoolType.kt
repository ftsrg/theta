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
package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.IffExpr
import hu.bme.mit.theta.core.type.NeqExpr
import hu.bme.mit.theta.core.type.abstracttype.Equational
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("bool")
object BoolType : Equational<BoolType> {

  private const val HASH_SEED = 754364
  private const val TYPE_LABEL = "Bool"

  @JvmStatic fun getInstance(): BoolType = this

  override fun hashCode(): Int = HASH_SEED

  override fun equals(other: Any?): Boolean = other != null && javaClass == other.javaClass

  override fun toString(): String = TYPE_LABEL

  override fun Eq(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): IffExpr =
    BoolExprs.Iff(leftOp, rightOp)

  override fun Neq(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): NeqExpr<BoolType> =
    BoolExprs.Xor(leftOp, rightOp)

  override val domainSize: DomainSize
    get() = DomainSize.TWO
}
