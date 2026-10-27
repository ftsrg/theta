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
package hu.bme.mit.theta.core.type.inttype

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.IntAddExpr
import hu.bme.mit.theta.core.type.IntDivExpr
import hu.bme.mit.theta.core.type.IntEqExpr
import hu.bme.mit.theta.core.type.IntGeqExpr
import hu.bme.mit.theta.core.type.IntGtExpr
import hu.bme.mit.theta.core.type.IntLeqExpr
import hu.bme.mit.theta.core.type.IntLtExpr
import hu.bme.mit.theta.core.type.IntMulExpr
import hu.bme.mit.theta.core.type.IntNegExpr
import hu.bme.mit.theta.core.type.IntNeqExpr
import hu.bme.mit.theta.core.type.IntPosExpr
import hu.bme.mit.theta.core.type.IntSubExpr
import hu.bme.mit.theta.core.type.ModExpr
import hu.bme.mit.theta.core.type.RemExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.Additive
import hu.bme.mit.theta.core.type.abstracttype.Castable
import hu.bme.mit.theta.core.type.abstracttype.Divisible
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative
import hu.bme.mit.theta.core.type.abstracttype.Ordered
import hu.bme.mit.theta.core.type.rattype.RatType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("int")
object IntType :
  Additive<IntType>,
  Multiplicative<IntType>,
  Divisible<IntType>,
  Equational<IntType>,
  Ordered<IntType>,
  Castable<IntType> {

  private const val HASH_SEED = 222670
  private const val TYPE_LABEL = "Int"

  @JvmStatic fun getInstance(): IntType = this

  override fun hashCode(): Int = HASH_SEED

  override fun equals(other: Any?): Boolean = other != null && javaClass == other.javaClass

  override fun toString(): String = TYPE_LABEL

  override fun Add(ops: Iterable<Expr<IntType>>): IntAddExpr = IntExprs.Add(ops)

  override fun Sub(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntSubExpr =
    IntExprs.Sub(leftOp, rightOp)

  override fun Pos(op: Expr<IntType>): IntPosExpr = IntExprs.Pos(op)

  override fun Neg(op: Expr<IntType>): IntNegExpr = IntExprs.Neg(op)

  override fun Mul(ops: Iterable<Expr<IntType>>): IntMulExpr = IntExprs.Mul(ops)

  override fun Div(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntDivExpr =
    IntExprs.Div(leftOp, rightOp)

  override fun Mod(leftOp: Expr<IntType>, rightOp: Expr<IntType>): ModExpr<IntType> =
    IntExprs.Mod(leftOp, rightOp)

  override fun Rem(leftOp: Expr<IntType>, rightOp: Expr<IntType>): RemExpr<IntType> =
    IntExprs.Rem(leftOp, rightOp)

  override fun Eq(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntEqExpr =
    IntExprs.Eq(leftOp, rightOp)

  override fun Neq(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntNeqExpr =
    IntExprs.Neq(leftOp, rightOp)

  override fun Lt(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntLtExpr =
    IntExprs.Lt(leftOp, rightOp)

  override fun Leq(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntLeqExpr =
    IntExprs.Leq(leftOp, rightOp)

  override fun Gt(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntGtExpr =
    IntExprs.Gt(leftOp, rightOp)

  override fun Geq(leftOp: Expr<IntType>, rightOp: Expr<IntType>): IntGeqExpr =
    IntExprs.Geq(leftOp, rightOp)

  @Suppress("UNCHECKED_CAST")
  override fun <TargetType : Type> Cast(op: Expr<IntType>, type: TargetType): Expr<TargetType> =
    if (type is RatType) IntExprs.ToRat(op) as Expr<TargetType>
    else throw ClassCastException("Int cannot be cast to $type")

  override val domainSize: DomainSize
    get() = DomainSize.INFINITY
}
