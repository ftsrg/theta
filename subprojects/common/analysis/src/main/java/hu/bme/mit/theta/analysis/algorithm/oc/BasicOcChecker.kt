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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus
import java.util.*

class BasicOcChecker<E : Event>(smtSolver: String) : OcCheckerBase<E>() {
  override val solver: Solver = SolverManager.resolveSolverFactory(smtSolver).createSolver()
  private var relations: GlobalRelation? = null

  /**
   * A decision together with the address conditions of the edges derived at it. Unlike relations
   * and events, these can change between models without undoing any decision, so they are checked
   * separately to keep the derived edges of the stack sound.
   */
  private class BasicOcAssignment<E : Event>(
    rels: GlobalRelation,
    relation: Relation<E>? = null,
    event: E? = null,
  ) : OcAssignment<E>(rels, relation, event) {
    val interferences = mutableListOf<Expr<BoolType>>()
  }

  override fun check(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): SolverStatus? {
    var modifiableRels = rfs.values.flatten() // modifiable relation vars
    val flatEvents = events.values.flatMap { it.values.flatten() }
    val decisionStack = Stack<BasicOcAssignment<E>>()
    decisionStack.push(BasicOcAssignment(getInitialRels(ppos))) // not really a decision point
    var finalWsCheck = false

    dpllLoop@ while (solver.check().isSat) { // DPLL loop
      val model = solver.model
      val valuation = model.toMap()

      val disabledRels = modifiableRels.filter { it.enabled(valuation) != true }
      val disabledEvents = flatEvents.filter { it.enabled(solver.model) != true }
      val firstDisabled =
        decisionStack.indexOfFirst { d ->
          d.relation?.let { it in disabledRels } == true ||
            d.event?.let { it in disabledEvents } == true ||
            d.interferences.any { !it.holds(model) }
        }
      if (firstDisabled >= 0) {
        while (decisionStack.size > firstDisabled) decisionStack.pop()
      }

      val enabledRels =
        modifiableRels.filter { rel ->
          rel.enabled(valuation) == true && decisionStack.none { it.relation == rel }
        }
      val enabledEvents =
        flatEvents.filter { ev ->
          if (ev.type != EventType.WRITE || !rfs.containsKey(ev.const.varDecl)) return@filter false
          ev.enabled(solver.model) == true && decisionStack.none { it.event == ev }
        }

      // propagate
      for (rel in enabledRels) {
        val assignment = BasicOcAssignment(decisionStack.peek().rels.copy(), relation = rel)
        decisionStack.push(assignment)
        val reason0 = setAndClose(assignment.rels, rel)
        if (propagate(reason0)) continue@dpllLoop

        when (rel.type) {
          RelationType.RF -> {
            val writes =
              events[rel.from.const.varDecl]!!.values.flatten().filter { w ->
                w.type == EventType.WRITE && decisionStack.any { it.event == w }
              }
            for (w in writes) {
              val reason = derive(assignment, rel, w)
              if (propagate(reason)) continue@dpllLoop
            }
          }

          RelationType.WS -> {
            val matchingRfs =
              rfs[rel.from.const.varDecl]?.filter { rf ->
                rf.from == rel.from && decisionStack.any { it.relation == rf }
              } ?: emptyList()
            for (rf in matchingRfs) {
              val reason = derive(assignment, rf, rel.to)
              if (propagate(reason)) continue@dpllLoop
            }
          }

          else -> {}
        }
      }

      for (w in enabledEvents) {
        val decision = BasicOcAssignment(decisionStack.peek().rels.copy(), event = w)
        decisionStack.push(decision)
        for (rf in
          rfs[w.const.varDecl]!!.filter { rf -> decisionStack.any { it.relation == rf } }) {
          val reason = derive(decision, rf, w)
          if (propagate(reason)) continue@dpllLoop
        }
      }

      if (!finalWsCheck) {
        // no conflict found at this point, checking counterexample for SC
        val unassignedWss = finalWsCheck(decisionStack.peek().rels, wss)
        modifiableRels = modifiableRels + unassignedWss
        finalWsCheck = true
        continue@dpllLoop
      }

      relations = decisionStack.peek().rels
      return solver.status // no conflict found, counterexample is valid
    }

    relations = decisionStack.peek().rels
    return solver.status
  }

  override fun getHappensBefore(): GlobalRelation? = relations?.copy()

  private fun derive(assignment: BasicOcAssignment<E>, rf: Relation<E>, w: E): Reason? {
    if (rf.to.sameMemory(w)) rf.to.interferenceCond(w)?.let { assignment.interferences.add(it) }
    return derive(assignment.rels, rf, w)
  }

  private fun Expr<BoolType>.holds(model: Valuation): Boolean =
    try {
      (eval(model) as? BoolLitExpr)?.value == true
    } catch (_: Exception) {
      false
    }

  override fun propagate(reason: Reason?): Boolean {
    reason ?: return false
    propagated.add(reason)
    solver.add(BoolExprs.Not(reason.expr))
    return true
  }
}
