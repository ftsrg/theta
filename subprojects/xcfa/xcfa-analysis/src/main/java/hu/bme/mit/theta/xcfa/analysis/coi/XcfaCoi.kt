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
package hu.bme.mit.theta.xcfa.analysis.coi

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.analysis.por.extension
import hu.bme.mit.theta.xcfa.analysis.por.nullableExtension
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.VarAccessMap
import hu.bme.mit.theta.xcfa.utils.collectAssumesVars
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.isRead
import hu.bme.mit.theta.xcfa.utils.isWritten
import hu.bme.mit.theta.xcfa.utils.pointsTo
import java.util.*
import kotlin.math.min

lateinit var ConeOfInfluence: XcfaCoi

internal typealias S = XcfaState<out PtrState<out ExprState>>

internal typealias A = XcfaAction

internal var XcfaAction.transFuncVersion: XcfaAction? by nullableExtension()

abstract class XcfaCoi(protected val xcfa: XCFA) {

  var coreLts: LTS<S, A> = getXcfaLts()
  lateinit var coreTransFunc: TransFunc<S, A, XcfaPrec<out Prec>>

  protected var lastPrec: Prec? = null
  protected var XcfaLocation.scc: Int by extension()
  protected val directObservers: MutableMap<XcfaEdge, Set<XcfaEdge>> = mutableMapOf()

  abstract val lts: LTS<S, A>

  val transFunc =
    TransFunc<S, A, XcfaPrec<out Prec>> { state, action, prec ->
      coreTransFunc.getSuccStates(state, action.transFuncVersion ?: action, prec)
    }

  init {
    xcfa.procedures.forEach { tarjan(it.initLoc) }
  }

  private fun tarjan(initLoc: XcfaLocation) {
    var sccCnt = 0
    var discCnt = 0
    val disc = mutableMapOf<XcfaLocation, Int>()
    val lowest = mutableMapOf<XcfaLocation, Int>()
    val visited = mutableSetOf<XcfaLocation>()
    val stack = Stack<XcfaLocation>()
    val toVisit = Stack<XcfaLocation>()
    toVisit.push(initLoc)

    while (toVisit.isNotEmpty()) {
      val visiting = toVisit.peek()
      if (visiting !in visited) {
        disc[visiting] = discCnt++
        lowest[visiting] = disc[visiting]!!
        stack.push(visiting)
        visited.add(visiting)
      }

      for (edge in visiting.outgoingEdges) {
        if (edge.target in stack) {
          lowest[visiting] = min(lowest[visiting]!!, lowest[edge.target]!!)
        } else if (edge.target !in visited) {
          toVisit.push(edge.target)
          break
        }
      }

      if (toVisit.peek() != visiting) continue

      if (lowest[visiting] == disc[visiting]) {
        val scc = sccCnt++
        while (stack.peek() != visiting) {
          stack.pop().scc = scc
        }
        stack.pop().scc = scc // visiting
      }

      toVisit.pop()
    }
  }

  protected fun findDirectObservers(edge: XcfaEdge, prec: Prec) {
    val precVars = prec.usedVars
    val writtenVars =
      edge.collectVarsWithAccessType().filter {
        it.value.isWritten && it.key in precVars
      } // TODO deref it.key in prec?
    if (writtenVars.isEmpty()) return
    val writtenMemLocs = writtenVars.pointsTo(xcfa)

    val toVisit = edge.target.outgoingEdges.toMutableList()
    val visited = mutableSetOf<XcfaEdge>()
    while (toVisit.isNotEmpty()) {
      val visiting = toVisit.removeFirst()
      visited.add(visiting)
      val currentVars = visiting.collectVarsWithAccessType()
      addEdgeIfObserved(
        edge,
        visiting,
        writtenVars,
        writtenMemLocs,
        precVars,
        directObservers,
        currentVars,
      )

      if (writtenMemLocs.size <= 1) {
        val currentWrites = currentVars.filter { it.value.isWritten }.map { it.key }
        if (writtenVars.all { it.key in currentWrites }) {
          val currentMemWrites = currentWrites.pointsTo(xcfa)
          if (currentMemWrites.size <= 1 && writtenMemLocs.all { it in currentMemWrites }) {
            continue
          }
        }
      }

      toVisit.addAll(visiting.target.outgoingEdges.filter { it !in visited })
    }
  }

  protected open fun addEdgeIfObserved(
    source: XcfaEdge,
    target: XcfaEdge,
    observableVars: VarAccessMap,
    writtenMemLocs: Set<LitExpr<*>>,
    precVars: Collection<VarDecl<*>>,
    relation: MutableMap<XcfaEdge, Set<XcfaEdge>>,
    vars: VarAccessMap = target.collectVarsWithAccessType(),
  ) {
    var relevantAction = vars.any { it.value.isWritten && it.key in precVars }
    if (!relevantAction) {
      val assumeVars = target.label.collectAssumesVars()
      relevantAction = assumeVars.any { it in precVars }
    }

    val readVars = vars.filter { it.value.isRead }
    if (
      relevantAction &&
        (readVars.any { it.key in observableVars } ||
          readVars.pointsTo(xcfa).any { it in writtenMemLocs })
    ) {
      addToRelation(source, target, relation)
    }
  }

  protected abstract fun addToRelation(
    source: XcfaEdge,
    target: XcfaEdge,
    relation: MutableMap<XcfaEdge, Set<XcfaEdge>>,
  )

  protected fun isRealObserver(edge: XcfaEdge) = edge.label.collectAssumesVars().isNotEmpty()

  protected fun replace(action: A, prec: Prec): XcfaAction {
    val replacedLabel = action.label.replace(prec)
    action.transFuncVersion =
      action.withLabel(
        replacedLabel.run { if (this !is SequenceLabel) SequenceLabel(listOf(this)) else this }
      )
    return action
  }

  private fun XcfaLabel.replace(prec: Prec): XcfaLabel =
    when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.replace(prec) }, metadata)
      is NondetLabel -> NondetLabel(labels.map { it.replace(prec) }.toSet(), metadata)
      is StmtLabel -> {
        when (val stmt = this.stmt) {
          is AssignStmt<*> ->
            if (stmt.varDecl in prec.usedVars) {
              StmtLabel(HavocStmt.of(stmt.varDecl), metadata = this.metadata)
            } else {
              NopLabel
            }

          is HavocStmt<*> ->
            if (stmt.varDecl in prec.usedVars) {
              this
            } else {
              NopLabel
            }

          else -> this
        }
      }

      else -> this
    }
}
