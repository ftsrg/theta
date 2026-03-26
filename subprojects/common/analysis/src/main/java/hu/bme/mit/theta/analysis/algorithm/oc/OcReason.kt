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

package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.TrueExpr

/** Reason(s) of an enabled relation. */
sealed class Reason {

  open val reasons: List<Reason>
    get() = listOf(this)

  protected open val expressions: List<Expr<BoolType>>
    get() = reasons.flatMap { it.expressions }

  val exprs: List<Expr<BoolType>>
    get() = expressions.filter { it !is TrueExpr }

  val expr: Expr<BoolType>
    get() = exprs.toAnd()

  infix fun and(other: Reason): Reason = CombinedReason(reasons + other.reasons)

  override fun toString(): String = "[${reasons.joinToString("; ")}]"

  override fun hashCode(): Int = exprs.hashCode()

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is Reason) return false
    if (other.javaClass != javaClass) return false
    return exprs == other.exprs
  }
}

class CombinedReason(override val reasons: List<Reason>) : Reason()

object PoReason : Reason() {

  override val reasons = emptyList<Reason>()
  override val expressions: List<Expr<BoolType>> = listOf()
}

class RelationReason<E : Event>(val relation: Relation<E>) : Reason() {

  override val expressions: List<Expr<BoolType>> = listOf(relation.declRef)

  override fun toString(): String = "REL(${relation.decl.name})"
}

sealed class DerivedReason<E : Event>(
  val rf: Relation<E>,
  val w: E,
  private val wRfRelation: Reason,
  private val name: String,
) : Reason() {

  override val expressions: List<Expr<BoolType>> =
    listOfNotNull(rf.declRef, w.guardExpr, rf.from.interferenceCond(w)) + wRfRelation.exprs

  override fun toString(): String = "$name(${rf.decl.name}, ${w.const.name}, $wRfRelation)"

  override fun hashCode(): Int =
    31 * (31 * (31 + w.hashCode()) + rf.hashCode()) + wRfRelation.hashCode()

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is DerivedReason<*>) return false
    if (other.javaClass != javaClass) return false
    return w == other.w && rf == other.rf && wRfRelation == other.wRfRelation
  }
}

class WriteSerializationReason<E : Event>(rf: Relation<E>, w: E, val wBeforeRf: Reason) :
  DerivedReason<E>(rf, w, wBeforeRf, "WS")

class FromReadReason<E : Event>(rf: Relation<E>, w: E, val wAfterRf: Reason) :
  DerivedReason<E>(rf, w, wAfterRf, "FR")

object UndetailedReason : Reason()
