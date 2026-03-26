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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.solver.Solver

abstract class SmtOcChecker<E : Event> : OcChecker<E> {

  /** SMT solver of the OC checker. */
  abstract val solver: Solver

  protected fun <E : Event> addWsCond(ws1: Relation<E>, ws2: Relation<E>) {
    val wsGuard = And(ws1.from.guardExpr, ws1.to.guardExpr)
    val wsCond = { ws: Relation<E> -> Imply(ws.declRef, wsGuard) }
    solver.add(wsCond(ws1))
    solver.add(wsCond(ws2))
    solver.add(Imply(wsGuard, Or(ws1.declRef, ws2.declRef)))
  }
}

/**
 * This interface implements basic utilities for an ordering consistency checker such as derivation
 * rules and transitive closure operations.
 */
abstract class DerivingOcChecker<E : Event> : SmtOcChecker<E>() {

  protected val propagated: MutableList<Reason> = mutableListOf()

  override fun getPropagatedClauses() = propagated.toList()

  protected abstract fun propagate(reason: Reason?): Boolean

  protected fun derive(rels: GlobalRelation, rf: Relation<E>, w: E): Reason? =
    when {
      rf.from.clkId == rf.to.clkId -> null
      // rf within an atomic block
      w.clkId == rf.from.clkId || w.clkId == rf.to.clkId -> null
      // w within an atomic block with one of the rf ends
      !rf.to.sameMemory(w) -> null
      // different memory locations (checking with rf.to due to common memory garbage event)

      rels[w.clkId, rf.to.clkId] != null -> { // WS derivation
        val reason = WriteSerializationReason(rf, w, rels[w.clkId, rf.to.clkId]!!)
        rels.close(w.clkId, rf.from.clkId, reason)
      }

      rels[rf.from.clkId, w.clkId] != null -> { // FR derivation
        val reason = FromReadReason(rf, w, rels[rf.from.clkId, w.clkId]!!)
        rels.close(rf.to.clkId, w.clkId, reason)
      }

      else -> null
    }

  protected fun setAndClose(rels: GlobalRelation, rel: Relation<E>): Reason? {
    if (rel.from.clkId == rel.to.clkId) return null // within an atomic block
    return rels.close(
      rel.from.clkId,
      rel.to.clkId,
      if (rel.type == RelationType.PO) PoReason else RelationReason(rel),
    )
  }

  protected fun finalWsCheck(
    rels: GlobalRelation,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): List<Relation<E>> {
    val unassignedWss = mutableListOf<Relation<E>>()
    wss.forEach { (_, wsRels) ->
      unassignedWss.addAll(
        wsRels.filter { ws ->
          rels[ws.from.clkId, ws.to.clkId] == null && rels[ws.to.clkId, ws.from.clkId] == null
        }
      )
    }
    if (unassignedWss.isEmpty()) return emptyList()

    val unassignedCopy = unassignedWss.toMutableList()
    val pairs = mutableListOf<Pair<Relation<E>, Relation<E>>>()
    while (unassignedCopy.isNotEmpty()) {
      val ws = unassignedCopy.removeFirst()
      val pair = unassignedCopy.find { it.from == ws.to || it.to == ws.from }
      if (pair != null) {
        pairs.add(ws to pair)
        unassignedCopy.remove(pair)
      }
    }

    pairs.forEach { (ws1, ws2) -> addWsCond(ws1, ws2) }

    return unassignedWss
  }

  protected fun getInitialRels(ppos: BooleanGlobalRelation) =
    GlobalRelation(ppos.size) { (i, j) -> if (ppos[i, j]) PoReason else null }
}

/**
 * Represents the known value of an important element for ordering consistency checking. Such an
 * important element is either a relation (being enabled) or an event (being enabled - having a
 * guard that evaluates to true). The fix relations (closed by theory axioms) and the solver
 * decision stack level are also stored.
 */
open class OcAssignment<E : Event>
internal constructor(
  val rels: GlobalRelation,
  val relation: Relation<E>? = null,
  val event: E? = null,
) {

  internal constructor(rels: GlobalRelation, e: E) : this(rels.copy(), event = e)

  internal constructor(rels: GlobalRelation, r: Relation<E>) : this(rels.copy(), relation = r)

  override fun toString() = "OcAssignment(${relation ?: event})"
}
