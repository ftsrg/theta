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
package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.TrueExpr

/** Important! Empty collection is converted to true (not false). */
internal fun Collection<Expr<BoolType>>.toAnd(): Expr<BoolType> =
  when (size) {
    0 -> BoolExprs.True()
    1 -> first()
    else -> BoolExprs.And(this)
  }

enum class EventType {
  WRITE,
  READ,
}

abstract class Event(
  val const: IndexedConstDecl<*>,
  val type: EventType,
  var guard: Set<Expr<BoolType>>,
  val pid: Int,
  val clkId: Int,
) {
  companion object {
    var clkSize = 0
      private set
  }

  init {
    if (clkId >= clkSize) {
      clkSize = clkId + 1
    }
  }

  val guardExpr: Expr<BoolType>
    get() = guard.toAnd()

  var assignment: Expr<BoolType>? = null
  var enabled: Boolean? = null

  open fun enabled(valuation: Valuation): Boolean? {
    val e = tryOrNull { (guardExpr.eval(valuation) as? BoolLitExpr)?.value }
    enabled = e
    return e
  }

  open fun sameMemory(other: Event): Boolean {
    if (this === other) return true
    return const.varDecl == other.const.varDecl
  }

  open fun interferenceCond(other: Event): Expr<BoolType>? = null

  protected inline fun <T> tryOrNull(block: () -> T?): T? =
    try {
      block()
    } catch (e: Exception) {
      null
    }

  override fun toString(): String {
    return "Event(pid=$pid, clkId=$clkId, ${const.name}[${type.toString()[0]}], guard=$guard)"
  }
}

enum class RelationType {
  PO,
  RF,
  WS,
}

data class Relation<E : Event>(val type: RelationType, val from: E, val to: E) {

  val decl: ConstDecl<BoolType> =
    Decls.Const(
      "${type.toString().lowercase()}_${from.const.name}_${to.const.name}",
      BoolExprs.Bool(),
    )
  val declRef: RefExpr<BoolType> = RefExpr.of(decl)
  var enabled: Boolean? = null

  override fun toString() =
    "Relation($type, ${from.const.name}[${from.type.toString()[0]}], ${to.const.name}[${to.type.toString()[0]}])"

  fun enabled(valuation: Map<Decl<*>, LitExpr<*>>): Boolean? {
    enabled =
      if (type == RelationType.PO) true else valuation[decl]?.let { (it as BoolLitExpr).value }
    return enabled
  }
}

/** Reason(s) of an enabled relation. */
sealed class Reason {

  open val reasons: List<Reason>
    get() = listOf(this)

  protected open val expressions: List<Expr<BoolType>>
    get() = reasons.map { it.expressions }.flatten()

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
