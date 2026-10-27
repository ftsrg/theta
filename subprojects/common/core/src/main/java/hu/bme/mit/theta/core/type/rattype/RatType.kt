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
package hu.bme.mit.theta.core.type.rattype

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.RatAddExpr
import hu.bme.mit.theta.core.type.RatDivExpr
import hu.bme.mit.theta.core.type.RatEqExpr
import hu.bme.mit.theta.core.type.RatGeqExpr
import hu.bme.mit.theta.core.type.RatGtExpr
import hu.bme.mit.theta.core.type.RatLeqExpr
import hu.bme.mit.theta.core.type.RatLtExpr
import hu.bme.mit.theta.core.type.RatMulExpr
import hu.bme.mit.theta.core.type.RatNegExpr
import hu.bme.mit.theta.core.type.RatNeqExpr
import hu.bme.mit.theta.core.type.RatPosExpr
import hu.bme.mit.theta.core.type.RatSubExpr
import hu.bme.mit.theta.core.type.abstracttype.Additive
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative
import hu.bme.mit.theta.core.type.abstracttype.Ordered
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("rat")
object RatType : Additive<RatType>, Multiplicative<RatType>, Equational<RatType>, Ordered<RatType> {

  private const val HASH_SEED = 385863
  private const val TYPE_LABEL = "Rat"

  @JvmStatic fun getInstance(): RatType = this

  override fun hashCode(): Int = HASH_SEED

  override fun equals(other: Any?): Boolean = other != null && javaClass == other.javaClass

  override fun toString(): String = TYPE_LABEL

  override fun Add(ops: Iterable<Expr<RatType>>): RatAddExpr = RatExprs.Add(ops)

  override fun Sub(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatSubExpr =
    RatExprs.Sub(leftOp, rightOp)

  override fun Pos(op: Expr<RatType>): RatPosExpr = RatExprs.Pos(op)

  override fun Neg(op: Expr<RatType>): RatNegExpr = RatExprs.Neg(op)

  override fun Mul(ops: Iterable<Expr<RatType>>): RatMulExpr = RatExprs.Mul(ops)

  override fun Div(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatDivExpr =
    RatExprs.Div(leftOp, rightOp)

  override fun Eq(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatEqExpr =
    RatExprs.Eq(leftOp, rightOp)

  override fun Neq(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatNeqExpr =
    RatExprs.Neq(leftOp, rightOp)

  override fun Lt(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatLtExpr =
    RatExprs.Lt(leftOp, rightOp)

  override fun Leq(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatLeqExpr =
    RatExprs.Leq(leftOp, rightOp)

  override fun Gt(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatGtExpr =
    RatExprs.Gt(leftOp, rightOp)

  override fun Geq(leftOp: Expr<RatType>, rightOp: Expr<RatType>): RatGeqExpr =
    RatExprs.Geq(leftOp, rightOp)

  override val domainSize: DomainSize
    get() = DomainSize.INFINITY
}
