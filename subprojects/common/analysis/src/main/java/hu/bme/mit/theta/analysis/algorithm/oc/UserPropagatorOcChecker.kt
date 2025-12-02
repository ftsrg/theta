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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverFactory
import hu.bme.mit.theta.solver.javasmt.JavaSMTUserPropagator
import java.util.*
import org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3

class UserPropagatorOcChecker<E : Event> : OcCheckerBase<E>() {

  private lateinit var writes: Map<VarDecl<*>, List<E>>
  private lateinit var rfs: Map<VarDecl<*>, Set<Relation<E>>>
  private lateinit var wss: Map<VarDecl<*>, Set<Relation<E>>>
  private lateinit var flatWrites: List<E>
  private lateinit var flatRfs: List<Relation<E>>
  private lateinit var flatWss: List<Relation<E>>
  private lateinit var interferenceCondToEvents: Map<Expr<BoolType>, List<Pair<E, E>>>
  private val partialAssignment = Stack<PropagatorOcAssignment<E>>()

  private val userPropagator: JavaSMTUserPropagator =
    object : JavaSMTUserPropagator() {
      override fun onKnownValue(expr: Expr<BoolType>, value: Boolean) {
        if (value) propagate(expr)
      }

      override fun onFinalCheck() =
        flatWrites
          .filter { w -> w.guard.isEmpty() || partialAssignment.any { it.event == w } }
          .forEach { w -> if (propagate(w)) return }

      override fun onPush() {
        solverLevel++
      }

      override fun onPop(levels: Int) = pop(levels)
    }

  private class PropagatorOcAssignment<E : Event>
  private constructor(
    stack: Stack<PropagatorOcAssignment<E>>,
    val solverLevel: Int,
    rels: GlobalRelation = stack.peek().rels.copy(),
    relation: Relation<E>? = null,
    event: E? = null,
    val interference: Pair<E, E>? = null,
  ) : OcAssignment<E>(rels, relation, event) {

    init {
      stack.push(this)
    }

    constructor(
      stack: Stack<PropagatorOcAssignment<E>>,
      rels: GlobalRelation,
    ) : this(stack, 0, rels)

    constructor(
      stack: Stack<PropagatorOcAssignment<E>>,
      e: E,
      solverLevel: Int,
    ) : this(stack, solverLevel, event = e)

    constructor(
      stack: Stack<PropagatorOcAssignment<E>>,
      r: Relation<E>,
      solverLevel: Int,
    ) : this(stack, solverLevel, relation = r)

    constructor(
      stack: Stack<PropagatorOcAssignment<E>>,
      i: Pair<E, E>,
      solverLevel: Int,
    ) : this(stack, solverLevel, interference = i)
  }

  override val solver: Solver =
    JavaSMTSolverFactory.create(Z3, arrayOf()).createSolverWithPropagators(userPropagator)
  private var solverLevel: Int = 0

  override fun check(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): SolverStatus? {
    writes =
      events.keys.associateWith { v ->
        events[v]!!.values.flatten().filter { it.type == EventType.WRITE }
      }
    flatWrites = this.writes.values.flatten()
    this.rfs = rfs
    flatRfs = rfs.values.flatten()
    this.wss = wss
    flatWss = wss.values.flatten()

    PropagatorOcAssignment(partialAssignment, getInitialRels(ppos))
    registerExpressions()

    val result = solver.check()
    if (result.isUnsat) return result
    return finalWsCheck() ?: return result
  }

  override fun getHappensBefore(): GlobalRelation? = partialAssignment.lastOrNull()?.rels?.copy()

  private fun registerExpressions() {
    flatRfs.forEach { rf -> userPropagator.registerExpression(rf.declRef) }
    flatWrites.forEach { w ->
      if (w.guard.isNotEmpty()) userPropagator.registerExpression(w.guardExpr)
    }

    val interferenceToEvents = mutableMapOf<Expr<BoolType>, MutableList<Pair<E, E>>>()
    flatWrites.forEach { w1 ->
      flatWrites.forEach { w2 ->
        if (w1 != w2) {
          w1.interferenceCond(w2)?.let {
            userPropagator.registerExpression(it)
            interferenceToEvents.getOrPut(it) { mutableListOf() }.add(w1 to w2)
          }
        }
      }
    }
    interferenceCondToEvents = interferenceToEvents
  }

  private fun interferenceKnown(w1: E, w2: E) =
    w1.interferenceCond(w2) == null || partialAssignment.any { it.interference == w1 to w2 }

  private fun propagate(expr: Expr<BoolType>): Boolean {
    flatRfs
      .find { it.declRef == expr }
      ?.let { rf ->
        return propagate(rf)
      }
    flatWss
      .find { it.declRef == expr }
      ?.let { ws ->
        return propagate(ws)
      }
    flatWrites.filter { it.guardExpr == expr }.forEach { w -> if (propagate(w)) return true }
    interferenceCondToEvents[expr]?.forEach { (w1, w2) -> if (propagate(w1, w2)) return true }
    return false
  }

  private fun propagate(rel: Relation<E>): Boolean {
    val assignment = PropagatorOcAssignment(partialAssignment, rel, solverLevel)
    val reason0 = setAndClose(assignment.rels, rel)
    if (propagate(reason0)) return true

    when (rel.type) {
      RelationType.RF -> {
        writes[rel.from.const.varDecl]!!
          .filter { w ->
            (w.guard.isEmpty() || partialAssignment.any { it.event == w }) &&
              interferenceKnown(rel.from, w)
          }
          .forEach { w ->
            val reason = derive(assignment.rels, rel, w)
            if (propagate(reason)) return true
          }
      }

      RelationType.WS -> {
        rfs[rel.from.const.varDecl]
          ?.filter { rf -> rf.from == rel.from && partialAssignment.any { it.relation == rf } }
          ?.forEach { rf ->
            val reason = derive(assignment.rels, rf, rel.to)
            if (propagate(reason)) return true
          }
      }

      else -> {}
    }

    return false
  }

  private fun propagate(w: E): Boolean {
    check(w.type == EventType.WRITE)
    val assignment = PropagatorOcAssignment(partialAssignment, w, solverLevel)

    rfs[w.const.varDecl]
      ?.filter { rf ->
        partialAssignment.any { it.relation == rf } && interferenceKnown(rf.from, w)
      }
      ?.forEach { rf ->
        val reason = derive(assignment.rels, rf, w)
        if (propagate(reason)) return true
      }

    return false
  }

  private fun propagate(w1: E, w2: E): Boolean {
    check(w1.type == EventType.WRITE && w2.type == EventType.WRITE)
    val assignment = PropagatorOcAssignment(partialAssignment, w1 to w2, solverLevel)
    if (partialAssignment.none { it.event == w1 } || partialAssignment.none { it.event == w2 })
      return false

    rfs[w1.const.varDecl]
      ?.filter { rf -> rf.from == w1 && partialAssignment.any { it.relation == rf } }
      ?.forEach { rf ->
        val reason = derive(assignment.rels, rf, w2)
        if (propagate(reason)) return true
      }

    return false
  }

  override fun propagate(reason: Reason?): Boolean {
    reason ?: return false
    propagated.add(reason)
    userPropagator.propagateConflict(reason.exprs)
    return true
  }

  private fun pop(levels: Int) {
    solverLevel -= levels
    while (partialAssignment.isNotEmpty() && partialAssignment.peek().solverLevel > solverLevel) {
      partialAssignment.pop()
    }
  }

  private fun finalWsCheck(): SolverStatus? {
    val rels = partialAssignment.peek().rels
    val unassignedWss = finalWsCheck(rels, wss)
    unassignedWss.forEach { ws -> userPropagator.registerExpression(ws.declRef) }
    return solver.check()
  }
}
