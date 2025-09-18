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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.isWritten
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import kotlin.math.max

/**
 * Unrolls loops where the number of loop executions can be determined statically. The UNROLL_LIMIT
 * refers to the number of loop executions: loops that are executed more times than this limit are
 * not unrolled. Loops with unknown number of iterations are unrolled to FORCE_UNROLL_LIMIT
 * iterations (this way a safe result might not be valid).
 */
class LoopUnrollPass(alwaysForceUnroll: Int = -1) : ProcedurePass {

  companion object {

    var UNROLL_LIMIT = 1000
    var FORCE_UNROLL_LIMIT = -1

    private val solver: Solver = Z3SolverFactory.getInstance().createSolver()
  }

  private val forceUnrollLimit = max(FORCE_UNROLL_LIMIT, alwaysForceUnroll)

  private val testedLoops = mutableSetOf<Loop>()

  private data class Loop(
    val loopStart: XcfaLocation,
    val loopLocs: Set<XcfaLocation>,
    val loopEdges: Set<XcfaEdge>,
    val loopVar: VarDecl<*>?,
    val loopVarInit: XcfaEdge?,
    val loopVarModifiers: List<XcfaEdge>?,
    val loopStartEdges: List<XcfaEdge>,
    val exitEdges: Map<XcfaLocation, List<XcfaEdge>>,
    val properlyUnrollable: Boolean,
    val forceUnrollLimit: Int,
  ) {

    private class BasicStmtAction(private val stmt: Stmt) : StmtAction() {
      constructor(edge: XcfaEdge) : this(edge.label.toStmt())

      constructor(edges: List<XcfaEdge>) : this(SequenceLabel(edges.map { it.label }).toStmt())

      override fun getStmts() = listOf(stmt)
    }

    fun unroll(builder: XcfaProcedureBuilder, transFunc: ExplStmtTransFunc) {
      val count = count(transFunc)
      if (count != null) {
        unroll(builder, count, true)
      } else if (forceUnrollLimit != -1) {
        builder.setUnsafeUnroll()
        unroll(builder, forceUnrollLimit, false)
      }
    }

    fun unroll(builder: XcfaProcedureBuilder, count: Int, removeCond: Boolean) {
      (loopLocs - loopStart).forEach(builder::removeLoc)
      loopLocs.flatMap { it.outgoingEdges }.forEach(builder::removeEdge)

      var startLocation = loopStart
      for (i in 0 until count) {
        startLocation = copyBody(builder, startLocation, i, removeCond)
      }

      exitEdges[loopStart]?.forEach { edge ->
        val label = if (removeCond) edge.label.removeCondition() else edge.label
        builder.addEdge(XcfaEdge(startLocation, edge.target, label, edge.metadata))
      }
    }

    private fun count(transFunc: ExplStmtTransFunc): Int? {
      if (!properlyUnrollable) return null
      check(loopVar != null && loopVarModifiers != null && loopVarInit != null)
      check(loopStartEdges.size == 1)

      val prec = ExplPrec.of(listOf(loopVar))
      var state = ExplState.of(ImmutableValuation.empty())
      state = transFunc.getSuccStates(state, BasicStmtAction(loopVarInit), prec).first()

      var cnt = 0
      val loopCondAction = BasicStmtAction(loopStartEdges.first())
      while (!transFunc.getSuccStates(state, loopCondAction, prec).first().isBottom) {
        cnt++
        if (UNROLL_LIMIT in 0 until cnt) return null
        state = transFunc.getSuccStates(state, BasicStmtAction(loopVarModifiers), prec).first()
      }
      return cnt
    }

    private fun copyBody(
      builder: XcfaProcedureBuilder,
      startLoc: XcfaLocation,
      index: Int,
      removeCond: Boolean,
    ): XcfaLocation {
      val locs =
        loopLocs.associateWith {
          val loc = XcfaLocation("${it.name}_loop${index}", metadata = it.metadata)
          builder.addLoc(loc)
          loc
        }

      loopEdges.forEach {
        val newSource = if (it.source == loopStart) startLoc else locs[it.source]!!
        val newLabel =
          if (it.source == loopStart && removeCond) it.label.removeCondition() else it.label
        val edge = XcfaEdge(newSource, locs[it.target]!!, newLabel, it.metadata)
        builder.addEdge(edge)
      }

      exitEdges.forEach { (loc, edges) ->
        for (edge in edges) {
          if (removeCond && loc == loopStart) continue
          val source = if (loc == loopStart) startLoc else locs[loc]!!
          builder.addEdge(XcfaEdge(source, edge.target, edge.label, edge.metadata))
        }
      }

      return locs[loopStart]!!
    }

    private fun XcfaLabel.removeCondition(): XcfaLabel {
      val stmtToRemove =
        getFlatLabels().find {
          it is StmtLabel && it.stmt is AssumeStmt && (it.collectVars() - loopVar).isEmpty()
        }
      return when {
        this == stmtToRemove -> NopLabel
        this is SequenceLabel -> SequenceLabel(labels.map { it.removeCondition() }, metadata)
        else -> this
      }
    }
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val transFunc = ExplStmtTransFunc.create(solver, 1)
    while (true) {
      val loop = findLoop(builder.initLoc) ?: break
      loop.unroll(builder, transFunc)
      testedLoops.add(loop)
    }
    return builder
  }

  private fun findLoop(initLoc: XcfaLocation): Loop? { // DFS
    val stack = Stack<XcfaLocation>()
    val explored = mutableSetOf<XcfaEdge>()
    stack.push(initLoc)
    while (stack.isNotEmpty()) {
      val current = stack.peek()
      val edgesToExplore = current.outgoingEdges subtract explored
      if (edgesToExplore.isEmpty()) {
        stack.pop()
      } else {
        val edge = edgesToExplore.random()
        if (edge.target in stack) { // loop found
          getLoop(edge.target)?.let {
            return it
          }
        } else {
          stack.push(edge.target)
        }
        explored.add(edge)
      }
    }
    return null
  }

  /** Find a loop from the given start location that can be unrolled. */
  private fun getLoop(loopStart: XcfaLocation): Loop? {
    var properlyUnrollable = true
    if (loopStart.outgoingEdges.size != 2) {
      properlyUnrollable = false // more than two outgoing edges from the loop start not supported
    }

    val (loopLocations, loopEdges) = getLoopElements(loopStart)
    if (loopEdges.isEmpty()) return null // unsupported loop structure

    val loopCondEdges = loopStart.outgoingEdges.filter { it.target in loopLocations }
    if (loopCondEdges.size != 1)
      properlyUnrollable = false // more than one loop condition not supported

    // find the loop variable based on the outgoing edges from the loop start location
    val loopVar =
      loopStart.outgoingEdges
        .map {
          val vars = it.label.collectVarsWithAccessType()
          if (vars.size != 1) {
            null // multiple variables in the loop condition not supported
          } else {
            vars.keys.first()
          }
        }
        .reduce { v1, v2 -> if (v1 != v2) null else v1 }
    if (loopVar == null) properlyUnrollable = false

    val (loopVarInit, loopVarModifiers) =
      run {
        if (!properlyUnrollable) return@run null

        // find (a subset of) edges that are executed in every loop iteration
        var edge = loopStart.outgoingEdges.find { it.target in loopLocations }!!
        val necessaryLoopEdges = mutableSetOf(edge)
        while (edge.target.outgoingEdges.size == 1) {
          edge = edge.target.outgoingEdges.first()
          necessaryLoopEdges.add(edge)
        }
        val finalEdges = loopStart.incomingEdges.filter { it.source in loopLocations }
        if (finalEdges.size == 1) {
          edge = finalEdges.first()
          necessaryLoopEdges.add(edge)
          while (edge.source.incomingEdges.size == 1) {
            edge = edge.source.incomingEdges.first()
            necessaryLoopEdges.add(edge)
          }
        }

        // find edges that modify the loop variable
        val loopVarModifiers =
          loopEdges.filter {
            val vars = it.label.collectVarsWithAccessType()
            if (vars[loopVar].isWritten) {
              if (it !in necessaryLoopEdges || vars.size > 1)
                return@run null // loop variable modification cannot be determined statically
              true
            } else {
              false
            }
          }

        // find loop variable initialization before the loop
        lateinit var loopVarInit: XcfaEdge
        var loc = loopStart
        while (true) {
          val inEdges = loc.incomingEdges.filter { it.source !in loopLocations }
          if (inEdges.size != 1) return@run null
          val inEdge = inEdges.first()
          val vars = inEdge.label.collectVarsWithAccessType()
          if (vars[loopVar].isWritten) {
            if (vars.size > 1) return@run null
            loopVarInit = inEdge
            break
          }
          loc = inEdge.source
        }

        loopVarInit to loopVarModifiers
      }
        ?: run {
          properlyUnrollable = false
          null to null
        }

    val exits =
      loopLocations
        .mapNotNull { loc ->
          val exitEdges = loc.outgoingEdges.filter { it.target !in loopLocations }
          if (exitEdges.isEmpty()) null else (loc to exitEdges)
        }
        .toMap()
    return Loop(
        loopStart = loopStart,
        loopLocs = loopLocations,
        loopEdges = loopEdges,
        loopVar = loopVar,
        loopVarInit = loopVarInit,
        loopVarModifiers = loopVarModifiers,
        loopStartEdges = loopCondEdges,
        exitEdges = exits,
        properlyUnrollable = properlyUnrollable,
        forceUnrollLimit = forceUnrollLimit,
      )
      .also { if (it in testedLoops) return null }
  }

  /** Find loop locations and edges. */
  private fun getLoopElements(loopStart: XcfaLocation): Pair<Set<XcfaLocation>, Set<XcfaEdge>> {
    val backSearch: (XcfaLocation) -> Pair<Set<XcfaLocation>, List<XcfaEdge>>? =
      backSearch@{ startLoc ->
        val locs = mutableSetOf<XcfaLocation>()
        val edges = mutableListOf<XcfaEdge>()
        val toVisit = mutableListOf(startLoc)
        while (toVisit.isNotEmpty()) {
          val current = toVisit.removeFirst()
          if (current == loopStart) continue
          if (current.incomingEdges.size == 0) return@backSearch null // not part of the loop
          if (locs.add(current)) {
            edges.addAll(current.incomingEdges)
            toVisit.addAll(current.incomingEdges.map { it.source })
          }
        }
        locs to edges
      }

    val locs = mutableSetOf(loopStart)
    val edges = mutableSetOf<XcfaEdge>()
    loopStart.incomingEdges.forEach { incoming ->
      val (l, e) = backSearch(incoming.source) ?: return@forEach
      locs.addAll(l)
      edges.addAll(e)
      edges.add(incoming)
    }
    return locs to edges
  }
}
