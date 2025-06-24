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
package hu.bme.mit.theta.core.type.rattype

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.Additive
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative
import hu.bme.mit.theta.core.type.abstracttype.Ordered
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName(RatType.TYPE_LABEL)
object RatType :
  Additive<RatType>, Multiplicative<RatType>, Equational<RatType>, Ordered<RatType>, Type {
  internal const val TYPE_LABEL = "Rat"

  @JvmStatic fun getInstance(): RatType = this

  override fun toString(): String = TYPE_LABEL

  override fun Add(ops: Iterable<Expr<RatType>>) = RatAddExpr.of(ops)

  override fun Sub(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatSubExpr(leftOp, rightOp)

  override fun Pos(op: Expr<RatType>) = RatPosExpr(op)

  override fun Neg(op: Expr<RatType>) = RatNegExpr(op)

  override fun Mul(ops: Iterable<Expr<RatType>>) = RatMulExpr.of(ops)

  override fun Div(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatDivExpr(leftOp, rightOp)

  override fun Eq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatEqExpr(leftOp, rightOp)

  override fun Neq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatNeqExpr(leftOp, rightOp)

  override fun Lt(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatLtExpr(leftOp, rightOp)

  override fun Leq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatLeqExpr(leftOp, rightOp)

  override fun Gt(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatGtExpr(leftOp, rightOp)

  override fun Geq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatGeqExpr(leftOp, rightOp)

  override val domainSize: DomainSize = DomainSize.INFINITY
}
