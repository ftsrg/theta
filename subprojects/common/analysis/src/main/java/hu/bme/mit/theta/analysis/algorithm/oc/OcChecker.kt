/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.solver.SolverStatus

internal inline fun <reified T> Array<Array<T?>>.copy(): Array<Array<T?>> =
  Array(size) { i -> Array(size) { j -> this[i][j] } }

/**
 * This is an interface of an ordering consistency checker for concurrent systems (e.g., concurrent
 * programs).
 *
 * An ordering consistency checker takes a set an events and a set of relation between events. It
 * checks whether there is an inconsistency (a cycle in the event graph based on the relations)
 * subject to the constraints added to the SMT-solver.
 */
interface OcChecker<E : Event> {

  val solver: Solver

  /**
   * Checks the consistency of the event graph (i.e., if there is a partial order of events
   * satisfying the given constraints).
   *
   * @param events the set of events grouped by variables
   * @param pos the elements of the relation "program-order" (the relations always present based on
   *   the input model)
   * @param rfs the (possible) elements of the "read-from" relation (not all of these are
   *   necessarily enabled)
   * @return returns the status of the solver after running the consistency checking
   */
  fun check(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): SolverStatus?

  /**
   * Get the discovered relations represented by their reasons between the events (or more exactly
   * between atomic blocks, see Event::clkId)
   */
  fun getRelations(): Array<Array<Reason?>>?

  /**
   * Get the list of propagated conflict clauses (their negations were added to the solver) in the
   * form of reasons.
   */
  fun getPropagatedClauses(): List<Reason>
}

/**
 * This interface implements basic utilities for an ordering consistency checker such as derivation
 * rules and transitive closure operations.
 */
abstract class OcCheckerBase<E : Event> : OcChecker<E> {

  protected val propagated: MutableList<Reason> = mutableListOf()

  override fun getPropagatedClauses() = propagated.toList()

  protected abstract fun propagate(reason: Reason?): Boolean

  protected fun derive(rels: Array<Array<Reason?>>, rf: Relation<E>, w: E): Reason? =
    when {
      !rf.from.sameMemory(w) -> null // different referenced memory locations
      rf.from.clkId == rf.to.clkId -> null // rf within an atomic block
      w.clkId == rf.from.clkId || w.clkId == rf.to.clkId ->
        null // w within an atomic block with one of the rf ends

      rels[w.clkId][rf.to.clkId] != null -> { // WS derivation
        val reason = WriteSerializationReason(rf, w, rels[w.clkId][rf.to.clkId]!!)
        setAndClose(rels, w.clkId, rf.from.clkId, reason)
      }

      rels[rf.from.clkId][w.clkId] != null -> { // FR derivation
        val reason = FromReadReason(rf, w, rels[rf.from.clkId][w.clkId]!!)
        setAndClose(rels, rf.to.clkId, w.clkId, reason)
      }

      else -> null
    }

  protected fun setAndClose(rels: Array<Array<Reason?>>, rel: Relation<E>): Reason? {
    if (rel.from.clkId == rel.to.clkId) return null // within an atomic block
    return setAndClose(
      rels,
      rel.from.clkId,
      rel.to.clkId,
      if (rel.type == RelationType.PO) PoReason else RelationReason(rel),
    )
  }

  private fun setAndClose(
    rels: Array<Array<Reason?>>,
    from: Int,
    to: Int,
    reason: Reason,
  ): Reason? {
    if (from == to) return reason // cycle (self-loop) found
    val toClose = mutableListOf(from to to to reason)
    while (toClose.isNotEmpty()) {
      val (fromTo, r) = toClose.removeFirst()
      val (i1, i2) = fromTo
      check(i1 != i2)
      if (rels[i1][i2] != null) continue

      rels[i1][i2] = r
      rels[i2].forEachIndexed { i2next, b ->
        if (b != null && rels[i1][i2next] == null) { // i2 -> i2next, not i1 -> i2next
          val combinedReason = r and b
          if (i1 == i2next) return combinedReason // cycle (self-loop) found
          toClose.add(i1 to i2next to combinedReason)
        }
      }
      rels.forEachIndexed { i1previous, b ->
        if (
          b[i1] != null && rels[i1previous][i2] == null
        ) { // i1previous -> i1, not i1previous -> i2
          val combinedReason = r and b[i1]!!
          if (i1previous == i2) return combinedReason // cycle (self-loop) found
          toClose.add(i1previous to i2 to combinedReason)
        }
      }
    }
    return null
  }

  protected fun finalWsCheck(
    rels: Array<Array<Reason?>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): List<Relation<E>> {
    val unassignedWss = mutableListOf<Relation<E>>()
    wss.forEach { (_, wsRels) ->
      unassignedWss.addAll(
        wsRels.filter { ws ->
          rels[ws.from.clkId][ws.to.clkId] == null && rels[ws.to.clkId][ws.from.clkId] == null
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

    pairs.forEach { (ws1, ws2) ->
      val wsGuard = And(ws1.from.guardExpr, ws1.to.guardExpr)
      val wsCond = { ws: Relation<E> -> Imply(ws.declRef, wsGuard) }
      solver.add(wsCond(ws1))
      solver.add(wsCond(ws2))
      solver.add(Imply(wsGuard, Or(ws1.declRef, ws2.declRef)))
    }

    return unassignedWss
  }
}

/**
 * Represents the known value of an important element for ordering consistency checking. Such an
 * important element is either a relation (being enabled) or an event (being enabled - having a
 * guard that evaluates to true). The fix (closed by theory axioms) relations and the solver
 * decision stack level are also stored.
 */
open class OcAssignment<E : Event>
internal constructor(
  val rels: Array<Array<Reason?>>,
  val relation: Relation<E>? = null,
  val event: E? = null,
) {

  internal constructor(rels: Array<Array<Reason?>>, e: E) : this(rels.copy(), event = e)

  internal constructor(
    rels: Array<Array<Reason?>>,
    r: Relation<E>,
  ) : this(rels.copy(), relation = r)
}
