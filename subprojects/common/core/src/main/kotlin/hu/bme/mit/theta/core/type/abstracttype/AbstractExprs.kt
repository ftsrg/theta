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
package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.common.Try
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.BoolType

/** Factory and utility methods for abstract expressions over multiple types. */
@Suppress("FunctionName")
object AbstractExprs {
  @JvmStatic
  // General
  fun <T : Type> Ite(cond: Expr<BoolType>, then: Expr<*>, elze: Expr<*>): IteExpr<*> {
    val newOps: Pair<Expr<T>, Expr<T>> = unify(then, elze)
    val newThen = newOps.first
    val newElse = newOps.second
    return Exprs.Ite(cond, newThen, newElse)
  }

  @JvmStatic
  // Additive
  fun <T : Additive<T>> Add(ops: Iterable<Expr<*>>): AddExpr<T> {
    val opList = ops.toList()
    require(opList.isNotEmpty())
    val head = Utils.head(opList)
    val tail = Utils.tail(opList)
    return combineAdd(head, tail)
  }

  private fun <T : Additive<T>> combineAdd(head: Expr<*>, tail: List<Expr<*>>): AddExpr<T> =
    if (tail.isEmpty()) {
      val newOp: Expr<T> = bind(head)
      val newOps = getAddOps(newOp)
      val type = newOp.type
      type.Add(newOps)
    } else {
      val newHead = Utils.head(tail)
      val newTail = Utils.tail(tail)
      val unifiedOps: Pair<Expr<T>, Expr<T>> = unify(head, newHead)
      val newLeftOp = unifiedOps.first
      val newRightOp = unifiedOps.second
      val type = newLeftOp.type
      val newLeftOps = getAddOps(newLeftOp)
      val newOps = newLeftOps + newRightOp
      val newAddExpr = type.Add(newOps)
      combineAdd(newAddExpr, newTail)
    }

  private fun <T : Additive<T>> getAddOps(expr: Expr<T>): List<Expr<T>> =
    if (expr is AddExpr<*>) (expr as AddExpr<T>).ops else listOf(expr)

  @JvmStatic
  fun <T : Additive<T>> Sub(leftOp: Expr<*>, rightOp: Expr<*>): SubExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Sub(l, r) }

  @JvmStatic
  fun <T : Additive<T>> Pos(op: Expr<*>): PosExpr<*> {
    val tOp: Expr<T> = bind(op)
    return tOp.type.Pos(tOp)
  }

  @JvmStatic
  fun <T : Additive<T>> Neg(op: Expr<*>): NegExpr<*> {
    val tOp: Expr<T> = bind(op)
    return tOp.type.Neg(tOp)
  }

  // Multiplicative
  @JvmStatic
  fun <T : Multiplicative<T>> Mul(ops: Iterable<Expr<*>>): MulExpr<*> {
    val opList = ops.toList()
    require(opList.isNotEmpty())
    val head = Utils.head(opList)
    val tail = Utils.tail(opList)
    return combineMul<T>(head, tail)
  }

  private fun <T : Multiplicative<T>> combineMul(head: Expr<*>, tail: List<Expr<*>>): MulExpr<T> =
    if (tail.isEmpty()) {
      val newOp: Expr<T> = bind(head)
      val newOps = getMulOps(newOp)
      val type = newOp.type
      type.Mul(newOps)
    } else {
      val newHead = Utils.head(tail)
      val newTail = Utils.tail(tail)
      val unifiedOps: Pair<Expr<T>, Expr<T>> = unify(head, newHead)
      val newLeftOp = unifiedOps.first
      val newRightOp = unifiedOps.second
      val type = newLeftOp.type
      val newLeftOps = getMulOps(newLeftOp)
      val newOps = newLeftOps + newRightOp
      val newMulExpr = type.Mul(newOps)
      combineMul(newMulExpr, newTail)
    }

  private fun <T : Multiplicative<T>> getMulOps(expr: Expr<T>): List<Expr<T>> =
    if (expr is MulExpr<*>) (expr as MulExpr<T>).ops else listOf(expr)

  @JvmStatic
  fun <T : Multiplicative<T>> Div(leftOp: Expr<*>, rightOp: Expr<*>): DivExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Div(l, r) }

  // Divisible
  @JvmStatic
  fun <T : Divisible<T>> Mod(leftOp: Expr<*>, rightOp: Expr<*>): ModExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Mod(l, r) }

  @JvmStatic
  fun <T : Divisible<T>> Rem(leftOp: Expr<*>, rightOp: Expr<*>): RemExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Rem(l, r) }

  @JvmStatic
  // Equational
  fun <T : Equational<T>> Eq(leftOp: Expr<*>, rightOp: Expr<*>): EqExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Eq(l, r) }

  @JvmStatic
  fun <T : Equational<T>> Neq(leftOp: Expr<*>, rightOp: Expr<*>): NeqExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Neq(l, r) }

  @JvmStatic
  // Ordered
  fun <T : Ordered<T>> Lt(leftOp: Expr<*>, rightOp: Expr<*>): LtExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Lt(l, r) }

  @JvmStatic
  fun <T : Ordered<T>> Leq(leftOp: Expr<*>, rightOp: Expr<*>): LeqExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Leq(l, r) }

  @JvmStatic
  fun <T : Ordered<T>> Gt(leftOp: Expr<*>, rightOp: Expr<*>): GtExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Gt(l, r) }

  @JvmStatic
  fun <T : Ordered<T>> Geq(leftOp: Expr<*>, rightOp: Expr<*>): GeqExpr<*> =
    create(leftOp, rightOp) { type: T, l, r -> type.Geq(l, r) }

  // Convenience methods
  @JvmStatic
  fun <T : Additive<T>> Add(leftOp: Expr<*>, rightOp: Expr<*>): AddExpr<*> =
    Add<T>(listOf(leftOp, rightOp))

  @JvmStatic
  fun <T : Multiplicative<T>> Mul(leftOp: Expr<*>, rightOp: Expr<*>): MulExpr<*> =
    Mul<T>(listOf(leftOp, rightOp))

  // Helper methods

  private fun <T : Type, R : Expr<*>> create(
    leftOp: Expr<*>,
    rightOp: Expr<*>,
    create: (T, Expr<T>, Expr<T>) -> R,
  ): R {
    val newOps: Pair<Expr<T>, Expr<T>> = unify(leftOp, rightOp)
    val newLeftOp = newOps.first
    val newRightOp = newOps.second
    val type = newLeftOp.type
    return create(type, newLeftOp, newRightOp)
  }

  private fun <T : Type, T1 : Type, T2 : Type, C : Castable<C>> unify(
    expr1: Expr<T1>,
    expr2: Expr<T2>,
  ): Pair<Expr<T>, Expr<T>> {
    val type1 = expr1.type
    val type2 = expr2.type
    if (type1 == type2) {
      @Suppress("UNCHECKED_CAST") return bind(expr1, expr2 as Expr<T1>)
    }
    if (type1 is Castable<*>) {
      @Suppress("UNCHECKED_CAST") val cType1 = type1 as C

      @Suppress("UNCHECKED_CAST") val cExpr1 = expr1 as Expr<C>
      val tryToCast = Try.attempt { cType1.Cast(cExpr1, type2) }
      if (tryToCast.isSuccess) {
        val t2Expr1 = tryToCast.asSuccess().value
        return bind(t2Expr1, expr2)
      }
    }
    if (type2 is Castable<*>) {
      @Suppress("UNCHECKED_CAST") val cType2 = type2 as C

      @Suppress("UNCHECKED_CAST") val cExpr2 = expr2 as Expr<C>
      val tryToCast = Try.attempt { cType2.Cast(cExpr2, type1) }
      if (tryToCast.isSuccess) {
        val t1Expr2 = tryToCast.asSuccess().value
        return bind(expr1, t1Expr2)
      }
    }
    throw ClassCastException("Types $type1 and $type2 can not be unified")
  }

  @Suppress("UNCHECKED_CAST")
  private fun <TR : Type, TP : Type> bind(expr: Expr<TP>): Expr<TR> = expr as Expr<TR>

  @Suppress("UNCHECKED_CAST")
  private fun <TR : Type, TP : Type> bind(
    expr1: Expr<TP>,
    expr2: Expr<TP>,
  ): Pair<Expr<TR>, Expr<TR>> = Pair(expr1 as Expr<TR>, expr2 as Expr<TR>)
}
