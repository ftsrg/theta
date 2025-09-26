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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

internal typealias E = XcfaEvent

internal typealias R = Relation<XcfaEvent>

@Suppress("unused")
enum class OcDecisionProcedureType(
  internal val checker: (String, XcfaOcMemoryConsistencyModel) -> OcChecker<E>
) {

  IDL({ solver, mcm -> IDLOcChecker(solver, mcm == XcfaOcMemoryConsistencyModel.SC) }),
  BASIC({ solver, _ -> BasicOcChecker(solver) }),
  PROPAGATOR({ _, _ -> UserPropagatorOcChecker() }),
}

/** Important! Empty collection is converted to true (not false). */
internal fun Collection<Expr<BoolType>>.toAnd(): Expr<BoolType> =
  when (size) {
    0 -> BoolExprs.True()
    1 -> first()
    else -> And(this)
  }

/**
 * Takes the OR of the contained lists mapped to an AND expression. Simplifications are made based
 * on the list sizes.
 */
internal fun Collection<Set<Expr<BoolType>>>.toOrInSet(): Set<Expr<BoolType>> =
  when (size) {
    0 -> setOf()
    1 -> first()
    else -> setOf(Or(map { it.toAnd() }))
  }

/** Takes a relation matrix and a list of initial pairs in the relation and closes the relation. */
internal fun close(
  relation: Array<Array<Boolean>>,
  initials: List<Pair<Int, Int>>,
  cycleAllowed: Boolean = true,
) {
  val toClose = initials.toMutableList()
  while (toClose.isNotEmpty()) {
    val (from, to) = toClose.removeFirst()
    check(cycleAllowed || from != to) { "Self-loop not allowed." }
    if (relation[from][to]) continue

    relation[from][to] = true
    relation[to].forEachIndexed { i, b -> if (b && !relation[from][i]) toClose.add(from to i) }
    relation.forEachIndexed { i, b -> if (b[from] && !relation[i][to]) toClose.add(i to to) }
  }
}

internal class XcfaEvent(
  const: IndexedConstDecl<*>,
  type: EventType,
  guard: Set<Expr<BoolType>>,
  pid: Int,
  val edge: XcfaEdge,
  clkId: Int = uniqueClkId(),
  val array: Expr<*>? = null,
  val offset: Expr<*>? = null,
  val id: Int = uniqueId(),
) : Event(const, type, guard, pid, clkId) {

  private var arrayStatic: LitExpr<*>? = null
  private var offsetStatic: LitExpr<*>? = null
  private var arrayLit: LitExpr<*>? = null
  private var offsetLit: LitExpr<*>? = null

  init {
    check((array == null && offset == null) || (array != null && offset != null)) {
      "Array and offset expressions must be both null or both non-null."
    }
    arrayStatic = tryOrNull { array?.eval(ImmutableValuation.empty()) }
    offsetStatic = tryOrNull { offset?.eval(ImmutableValuation.empty()) }
  }

  companion object {

    private var idCnt: Int = 0
    private var clkCnt: Int = 0

    private fun uniqueId(): Int = idCnt++

    internal fun uniqueClkId(): Int = clkCnt++
  }

  // A (memory) event is only considered enabled if the array and offset expressions are also known
  override fun enabled(valuation: Valuation): Boolean? {
    when (val e = super.enabled(valuation)) {
      null,
      false -> return e
      true -> {
        if (array != null) {
          arrayLit = tryOrNull { array.eval(valuation) }
          if (arrayLit == null) return null
        }
        if (offset != null) {
          offsetLit = tryOrNull { offset.eval(valuation) }
          if (offsetLit == null) return null
        }
        return true
      }
    }
  }

  override fun sameMemory(other: Event): Boolean {
    other as XcfaEvent
    if (arrayLit != other.arrayLit) return false
    if (offsetLit != other.offsetLit) return false
    return potentialSameMemory(other)
  }

  fun potentialSameMemory(other: XcfaEvent): Boolean {
    if (!super.sameMemory(other)) return false
    if (arrayStatic != null && other.arrayStatic != null && arrayStatic != other.arrayStatic)
      return false
    if (offsetStatic != null && other.offsetStatic != null && offsetStatic != other.offsetStatic)
      return false
    return true
  }

  override fun interferenceCond(other: Event): Expr<BoolType>? {
    other as XcfaEvent
    array ?: return null
    other.array ?: return null

    var arrayEq: Expr<BoolType>? = Eq(array, other.array)
    if (arrayStatic != null && other.arrayStatic != null) {
      if (arrayStatic != other.arrayStatic) return null
      arrayEq = null
    }

    var offsetEq: Expr<BoolType>? = Eq(offset, other.offset)
    if (offsetStatic != null && other.offsetStatic != null) {
      if (offsetStatic != other.offsetStatic) return null
      offsetEq = null
    }

    return listOfNotNull(arrayEq, offsetEq).toAnd()
  }
}

@Suppress("UNCHECKED_CAST")
internal val Reason.from: E
  get() =
    when (this) {
      is RelationReason<*> -> (this as RelationReason<E>).relation.from
      is WriteSerializationReason<*> -> (this as WriteSerializationReason<E>).w
      is FromReadReason<*> -> (this as FromReadReason<E>).rf.to
      else -> error("Unsupported reason type.")
    }

@Suppress("UNCHECKED_CAST")
internal val Reason.to: E
  get() =
    when (this) {
      is RelationReason<*> -> (this as RelationReason<E>).relation.to
      is WriteSerializationReason<*> -> (this as WriteSerializationReason<E>).rf.from
      is FromReadReason<*> -> (this as FromReadReason<E>).w
      else -> error("Unsupported reason type.")
    }

internal data class Violation(
  val errorLoc: XcfaLocation,
  val pid: Int,
  val guard: Expr<BoolType>,
  val lastEvents: List<XcfaEvent>,
)

internal data class Thread(
  val pid: Int = uniqueId(),
  val procedure: XcfaProcedure,
  val guard: Set<Expr<BoolType>> = setOf(),
  val pidVar: VarDecl<*>? = null,
  val startEvent: XcfaEvent? = null,
  val startHistory: List<String> = listOf(),
  val lastWrites: Map<VarDecl<*>, Set<E>> = mapOf(),
  val joinEvents: MutableSet<XcfaEvent> = mutableSetOf(),
) {

  val finalEvents: MutableSet<XcfaEvent> = mutableSetOf()

  companion object {

    private var cnt: Int = 0

    fun uniqueId(): Int = cnt++
  }
}

internal data class SearchItem(val loc: XcfaLocation) {

  val guards: MutableList<Set<Expr<BoolType>>> = mutableListOf()
  val lastEvents: MutableList<XcfaEvent> = mutableListOf()
  val lastWrites: MutableList<Map<VarDecl<*>, Set<XcfaEvent>>> = mutableListOf()
  val threadLookups: MutableList<Map<VarDecl<*>, Set<Pair<Set<Expr<BoolType>>, Thread>>>> =
    mutableListOf()
  val atomics: MutableList<Int?> = mutableListOf()
  var incoming: Int = 0
}

internal data class StackItem(val event: XcfaEvent) {

  var eventsToVisit: MutableList<XcfaEvent>? = null
}
