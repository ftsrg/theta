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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.utils.StmtSimplifier
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.XcfaScope
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.getLoopElements
import hu.bme.mit.theta.xcfa.passes.loopEdges
import java.util.*
import kotlin.collections.component1
import kotlin.collections.component2
import kotlin.collections.get
import kotlin.collections.none

/** Get flattened label list (without sequence labels). */
fun XcfaEdge.getFlatLabels(): List<XcfaLabel> = label.getFlatLabels()

fun XcfaLabel.getFlatLabels(): List<XcfaLabel> =
  when (this) {
    is SequenceLabel -> {
      val ret = mutableListOf<XcfaLabel>()
      labels.forEach { ret.addAll(it.getFlatLabels()) }
      ret
    }

    else -> listOf(this)
  }

fun XCFA.getSymbols(): Pair<XcfaScope, Env> {
  val symbolTable = SymbolTable()
  val scope = XcfaScope(symbolTable)
  val vars = collectVars()
  val env = Env()
  vars.forEach {
    val symbol = Symbol { it.name }
    symbolTable.add(symbol)
    env.define(symbol, it)
  }
  return Pair(scope, env)
}

/**
 * Returns XCFA locations that are inner locations of any atomic block (after an edge with an
 * AtomicBegin and before an edge with an AtomicEnd) for all procedures of the XCFA.
 *
 * @param builder the XCFA builder
 * @return the set of locations in an atomic block in all procedures of the XCFA
 */
fun getAtomicBlockInnerLocations(builder: XcfaBuilder): Set<XcfaLocation> =
  builder.getProcedures().flatMap { getAtomicBlockInnerLocations(it) }.toSet()

/**
 * Returns XCFA locations that are inner locations of any atomic block (after an edge with an
 * AtomicBegin and before an edge with an AtomicEnd).
 *
 * @param builder the atomic block inner locations of the procedure of this builder will be returned
 * @return the list of locations in an atomic block
 */
fun getAtomicBlockInnerLocations(builder: XcfaProcedureBuilder): List<XcfaLocation> =
  getAtomicBlockInnerLocations(builder.initLoc)

private fun getAtomicBlockInnerLocations(initialLocation: XcfaLocation): List<XcfaLocation> {
  val atomicLocations = mutableListOf<XcfaLocation>()
  val visitedLocations = mutableListOf<XcfaLocation>()
  val locationsToVisit = mutableListOf(initialLocation)
  val isAtomic = mutableMapOf(initialLocation to false)
  while (locationsToVisit.isNotEmpty()) {
    val visiting = locationsToVisit.removeAt(0)
    if (checkNotNull(isAtomic[visiting])) atomicLocations.add(visiting)
    visitedLocations.add(visiting)
    for (outEdge in visiting.outgoingEdges) {
      var isNextAtomic = checkNotNull(isAtomic[visiting])
      if (outEdge.getFlatLabels().any { it.isAtomicBegin }) {
        isNextAtomic = true
      }
      if (outEdge.getFlatLabels().any { it.isAtomicEnd }) {
        isNextAtomic = false
      }
      val target = outEdge.target
      isAtomic[target] = isNextAtomic
      if (target in atomicLocations && !isNextAtomic) {
        atomicLocations.remove(target)
      }
      if (target !in locationsToVisit && target !in visitedLocations) {
        locationsToVisit.add(outEdge.target)
      }
    }
  }
  return atomicLocations
}

fun XcfaLabel.simplify(valuation: MutableValuation, parseContext: ParseContext): XcfaLabel =
  if (this is StmtLabel) {
    val simplified = stmt.accept(StmtSimplifier.StmtSimplifierVisitor(), valuation).stmt
    when (stmt) {
      is MemoryAssignStmt<*, *, *> -> {
        simplified as MemoryAssignStmt<*, *, *>
        if (parseContext.metadata.getMetadataValue(stmt.expr, "cType").isPresent)
          parseContext.metadata.create(
            simplified.expr,
            "cType",
            CComplexType.getType(stmt.expr, parseContext),
          )
        if (parseContext.metadata.getMetadataValue(stmt.deref, "cType").isPresent)
          parseContext.metadata.create(
            simplified.deref,
            "cType",
            CComplexType.getType(stmt.deref, parseContext),
          )
        StmtLabel(simplified, metadata = metadata)
      }

      is AssignStmt<*> -> {
        simplified as AssignStmt<*>
        if (parseContext.metadata.getMetadataValue(stmt.expr, "cType").isPresent)
          parseContext.metadata.create(
            simplified.expr,
            "cType",
            CComplexType.getType(stmt.expr, parseContext),
          )
        StmtLabel(simplified, metadata = metadata)
      }

      is AssumeStmt -> {
        simplified as AssumeStmt
        if (parseContext.metadata.getMetadataValue(stmt.cond, "cType").isPresent) {
          parseContext.metadata.create(
            simplified.cond,
            "cType",
            CComplexType.getType(stmt.cond, parseContext),
          )
        }
        parseContext.metadata.create(simplified, "cTruth", stmt.cond is NeqExpr<*>)
        StmtLabel(simplified, metadata = metadata, choiceType = choiceType)
      }

      else -> this
    }
  } else this

/**
 * Returns the set of edges that are before any thread start in the init procedure or after all
 * thread joins in the init procedure (when it is guaranteed that no other thread is running).
 *
 * @param builder the XcfaBuilder to analyze
 * @param onlyInitPhase if true, only edges before any thread start are returned
 * @return the set of init and final phase edges (before all thread starts and after all thread
 *   joins) if applicable
 */
fun getNonConcurrentEdges(
  builder: XcfaBuilder,
  onlyInitPhase: Boolean = false,
): Pair<Set<XcfaEdge>, Set<XcfaEdge>?> {
  val initProcedure = builder.getInitProcedures().first().first
  val loopEdges = initProcedure.loopEdges
  var potentialNotJoinedThread =
    loopEdges.any { edge ->
      edge.getFlatLabels().any { it is StartLabel || it is JoinLabel || it is InvokeLabel }
    }

  val starts = mutableSetOf<XcfaEdge>()
  val startedThreadVars = mutableSetOf<VarDecl<*>>()
  val joins = mutableSetOf<XcfaEdge>()
  val joinedThreadVars = mutableSetOf<VarDecl<*>>()
  initProcedure.getEdges().forEach { edge ->
    edge.getFlatLabels().forEach { label ->
      if (label is StartLabel) {
        if (label.pidVar in startedThreadVars) {
          potentialNotJoinedThread = false
        }
        starts.add(edge)
        startedThreadVars.add(label.pidVar)
      }
      if (label is JoinLabel) {
        joins.add(edge)
        joinedThreadVars.add(label.pidVar)
      }
    }
  }

  if (starts.isEmpty()) {
    return setOf<XcfaEdge>() to null
  }

  // Collect edges before any thread start
  val edgesAfterAnyStart =
    starts
      .map { start -> collectReachableEdges(start, true) }
      .reduce { acc, edgesAfterStart -> acc union edgesAfterStart }
  val edgesBeforeAllStarts = initProcedure.getEdges() - edgesAfterAnyStart

  if (
    potentialNotJoinedThread || onlyInitPhase || !startedThreadVars.all { it in joinedThreadVars }
  ) {
    return edgesBeforeAllStarts to null
  }

  // Collect edges after all thread joins
  val edgesBeforeAnyJoin =
    joins
      .map { join -> collectReachableEdges(join, false) }
      .reduce { acc, edgesAfterJoin -> acc union edgesAfterJoin }
  val edgesAfterAllJoins = initProcedure.getEdges() - edgesBeforeAnyJoin

  return edgesBeforeAllStarts to edgesAfterAllJoins
}

private fun collectReachableEdges(start: XcfaEdge, forward: Boolean = true): Set<XcfaEdge> {
  val visited = mutableSetOf<XcfaLocation>()
  val toVisit = mutableListOf(if (forward) start.target else start.source)
  val reachableEdges = mutableSetOf(start)
  while (toVisit.isNotEmpty()) {
    val loc = toVisit.removeLast()
    if (!visited.add(loc)) continue
    val edges = if (forward) loc.outgoingEdges else loc.incomingEdges
    edges.forEach { edge ->
      reachableEdges.add(edge)
      toVisit.add(if (forward) edge.target else edge.source)
    }
  }
  return reachableEdges
}

fun getInitLoops(
  initLoc: XcfaLocation,
  initEdges: Set<XcfaEdge>,
): Map<XcfaLocation, Set<XcfaEdge>> {
  val loopEdges = mutableMapOf<XcfaLocation, Set<XcfaEdge>>()
  val visited = mutableSetOf<XcfaEdge>()
  val stack = Stack<XcfaLocation>()
  stack.push(initLoc)
  while (stack.isNotEmpty()) {
    val loc = stack.peek()
    val edge = loc.outgoingEdges.firstOrNull { it in initEdges && it !in visited }
    if (edge == null) {
      stack.pop()
      continue
    }
    visited.add(edge)
    if (edge.target in stack) {
      val (_, edges) = getLoopElements(edge)
      if (edges.all { it in initEdges }) {
        loopEdges[edge.target] = edges
      }
    } else {
      stack.push(edge.target)
    }
  }
  return loopEdges
}

private fun <T : Type> assignStmtLabelOf(
  lhs: VarDecl<T>,
  rhs: Expr<T>,
  metadata: MetaData = EmptyMetaData,
): StmtLabel = StmtLabel(Assign(lhs, rhs), metadata = metadata)

@Suppress("FunctionName")
fun <T1 : Type, T2 : Type> AssignStmtLabel(
  lhs: VarDecl<T1>,
  rhs: Expr<T2>,
  metadata: MetaData = EmptyMetaData,
): StmtLabel = assignStmtLabelOf(lhs, cast(rhs, lhs.type), metadata)

@Suppress("FunctionName")
fun <T1 : Type, T2 : Type, T3 : Type> AssignStmtLabel(
  lhs: VarDecl<T1>,
  rhs: Expr<T2>,
  type: T3,
  metadata: MetaData = EmptyMetaData,
): StmtLabel = assignStmtLabelOf(cast(lhs, type), cast(rhs, type), metadata)

@Suppress("FunctionName")
fun <T1 : Type, T2 : Type> AssignStmtLabel(
  lhs: RefExpr<T1>,
  rhs: Expr<T2>,
  metadata: MetaData = EmptyMetaData,
): StmtLabel = assignStmtLabelOf(cast(lhs.decl as VarDecl<*>, rhs.type), rhs, metadata)

fun intersect(v1: Valuation?, v2: Valuation?): Valuation {
  if (v1 == null || v2 == null) return ImmutableValuation.empty()
  val v1map = v1.toMap()
  val v2map = v2.toMap()
  return ImmutableValuation.from(
    v1map.filter { v2map.containsKey(it.key) && v2map[it.key] == it.value }
  )
}

infix fun Valuation?.union(other: Valuation?): Valuation {
  val map1 = this?.toMap() ?: mapOf()
  val map2 = other?.toMap() ?: mapOf()
  check((map1.keys intersect map2.keys).all { map1[it] == map2[it] })
  return ImmutableValuation.from(map1 + map2)
}

fun mergeIncomingValuations(
  loc: XcfaLocation,
  valuations: Map<XcfaEdge, Valuation>,
  initLoops: Map<XcfaLocation, Set<XcfaEdge>>,
): Valuation {
  val nonModifiedValuation =
    if (loc.incomingEdges.size == 2 && loc in initLoops) {
      val loopEdges = initLoops[loc]!!
      val previousNonLoopEdge = loc.incomingEdges.first { it !in loopEdges }
      ImmutableValuation.from(
        valuations[previousNonLoopEdge]?.toMap()?.filter { (v, _) ->
          loopEdges.none { e -> e.collectVarsWithAccessType()[v]?.isWritten == true }
        }
      )
    } else {
      null
    }
  val intersectedValuation =
    loc.incomingEdges
      .filter { it.getFlatLabels().none { l -> l is StmtLabel && l.stmt == Assume(False()) } }
      .map(valuations::get)
      .reduceOrNull(::intersect)
  return nonModifiedValuation union intersectedValuation
}
