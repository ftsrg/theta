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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level.INFO
import hu.bme.mit.theta.common.logging.Logger.Level.MAINSTEP
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.loopEdges

/**
 * Checks whether a data race is possible in the given XCFA
 *
 * @param xcfa the XCFA to analyze
 * @return true if there is any potential racing global variable or memory access that is not atomic
 *   where the variable/memory location is written at least once
 */
fun isDataRacePossible(xcfa: XCFA, logger: Logger? = null): Boolean {
  logger?.writeln(MAINSTEP, "Data race pre-check")
  logger?.writeln(MAINSTEP, "| Collecting candidates for data race...")
  val builder = xcfa.procedureBuilders.first().parent
  val (initEdges, finalEdges) = getNonConcurrentEdges(builder)
  val nonConcurrent = initEdges + (finalEdges ?: setOf())
  val atomicLocations = getAtomicBlockInnerLocations(builder)
  val potentialRacingVars = getPotentialRacingVars(builder, nonConcurrent, atomicLocations)
  if (potentialRacingVars.isNotEmpty()) {
    logger?.writeln(MAINSTEP, "| Potential racing global variable found.")
    logger?.writeln(INFO, "| Potential racing variables: $potentialRacingVars")
    return true
  }

  val pointerPartitions = pointerPartitions(xcfa, initEdges)
  val n = pointerPartitions.size
  val nonAtomicMemoryAccess = BooleanArray(n + 1) { false }
  val writeMemoryAccess = BooleanArray(n + 1) { false }
  builder.getProcedures().forEach { proc ->
    val edges = proc.getEdges() - nonConcurrent
    for (e in edges) {
      var atomic = e.source in atomicLocations
      for (l in e.getFlatLabels()) {
        if (l.isAtomicBegin) atomic = true
        if (l.isAtomicEnd) atomic = false
        l.dereferencesWithAccessType.forEach { (deref, access) ->
          val partition =
            pointerPartitions
              .indexOfFirst {
                ((deref.array as? RefExpr<*>)?.decl in it.first) || deref.array in it.second
              }
              .let { if (it == -1) n else it } // if not found, put in "other" partition
          if (!atomic) {
            nonAtomicMemoryAccess[partition] = true
          }
          if (access.isWritten) {
            writeMemoryAccess[partition] = true
          }
          if (nonAtomicMemoryAccess[partition] && writeMemoryAccess[partition]) {
            logger?.writeln(MAINSTEP, "| Potential racing memory location found.")
            return true
          }
        }
      }
    }
  }

  logger?.writeln(MAINSTEP, "| No candidate for data race.")
  return false
}

/**
 * Collects the set of variables that may be involved in a data race.
 *
 * @param builder the XcfaBuilder to analyze
 * @return the set of variables that may be involved in a data race
 */
fun getPotentialRacingVars(builder: XcfaBuilder): Set<VarDecl<*>> {
  val (initEdges, finalEdges) = getNonConcurrentEdges(builder)
  val nonConcurrent = initEdges + (finalEdges ?: setOf())
  return getPotentialRacingVars(builder, nonConcurrent, getAtomicBlockInnerLocations(builder))
}

/**
 * Collects the set of variables that may be involved in a data race.
 *
 * @param builder the XcfaBuilder to analyze
 * @param nonConcurrent the set of edges that are before any thread start in the init procedure
 * @param atomicLocations the set of locations that are inside atomic blocks
 * @return the set of variables that may be involved in a data race
 */
private fun getPotentialRacingVars(
  builder: XcfaBuilder,
  nonConcurrent: Set<XcfaEdge>,
  atomicLocations: Set<XcfaLocation>,
): Set<VarDecl<*>> {
  val multipleThreadsPerProcedure = getMultipleThreadsPerProcedure(builder)
  val nonAtomicGlobalVars = builder.getVars().filter { !it.atomic }.map { it.wrappedVar }.toSet()
  val threadsAccessingVar = nonAtomicGlobalVars.associateWith { 0 }.toMutableMap()
  val writeAccesses = nonAtomicGlobalVars.associateWith { false }.toMutableMap()
  val nonAtomicAccesses = nonAtomicGlobalVars.associateWith { false }.toMutableMap()

  for (proc in builder.getProcedures()) {
    val edges = proc.getEdges() - nonConcurrent
    val varAccessCount = if (multipleThreadsPerProcedure[proc] == true) 2 else 1
    val currentVarAccesses = mutableSetOf<VarDecl<*>>()
    for (e in edges) {
      var atomic = e.source in atomicLocations
      for (l in e.getFlatLabels()) {
        if (l.isAtomicBegin) atomic = true
        if (l.isAtomicEnd) atomic = false
        val accesses = l.collectVarsWithAccessType()
        accesses.forEach { (v, access) ->
          if (v in nonAtomicGlobalVars) {
            currentVarAccesses.add(v)
            if (access.isWritten) {
              writeAccesses[v] = true
            }
            if (!atomic) {
              nonAtomicAccesses[v] = true
            }
          }
        }
      }
    }
    currentVarAccesses.forEach { v ->
      threadsAccessingVar[v] = threadsAccessingVar[v]!! + varAccessCount
    }
  }

  val potentialRacingVars =
    nonAtomicGlobalVars
      .filter {
        threadsAccessingVar[it]!! > 1 && nonAtomicAccesses[it] == true && writeAccesses[it] == true
      }
      .toSet()
  return potentialRacingVars
}

/**
 * Collects the number of threads for each procedure: returns true if multiple threads may run the
 * procedure, false otherwise. Note that this is a conservative analysis.
 */
fun getMultipleThreadsPerProcedure(builder: XcfaBuilder): Map<XcfaProcedureBuilder, Boolean> {
  val threadCount = builder.getInitProcedures().associate { it.first to false }.toMutableMap()
  var previousCounts: Map<XcfaProcedureBuilder, Boolean>? = null
  while (previousCounts != threadCount) {
    previousCounts = threadCount.toMap()
    val visitedNewRound = mutableSetOf<XcfaProcedureBuilder>()
    builder.getProcedures().forEach { proc ->
      if (proc !in threadCount) return@forEach
      val loopEdges = proc.loopEdges
      proc.getEdges().forEach { edge ->
        val originalCounts = visitedNewRound.toSet()
        edge.getFlatLabels().forEach { label ->
          if (label is StartLabel) {
            val started = builder.getProcedures().find { it.name == label.name }!!
            threadCount[started] =
              threadCount[started] == true ||
                threadCount[proc] == true ||
                started in visitedNewRound ||
                (edge in loopEdges)
            visitedNewRound.add(started)
          } else if (label is InvokeLabel) {
            val invoked = builder.getProcedures().find { it.name == label.name }!!
            threadCount[invoked] =
              threadCount[invoked] == true || threadCount[proc] == true || invoked in originalCounts
            visitedNewRound.add(invoked)
          }
        }
      }
    }
  }
  return threadCount
}

private fun pointerPartitions(
  xcfa: XCFA,
  initEdges: Set<XcfaEdge>,
): List<Pair<Set<VarDecl<*>>, Set<LitExpr<*>>>> {
  val pointsTo = xcfa.getPointsToGraph(initEdges).toList()

  val n = pointsTo.size
  val uf = UnionFind(n)

  val elementToSets = mutableMapOf<LitExpr<*>, MutableList<Int>>()
  pointsTo.forEachIndexed { index, (_, lits) ->
    lits.forEach { lit -> elementToSets.getOrPut(lit) { mutableListOf() }.add(index) }
  }

  elementToSets.forEach { (_, indices) ->
    for (i in 1 until indices.size) {
      uf.union(indices[0], indices[i])
    }
  }

  val groups = mutableMapOf<Int, Pair<MutableSet<VarDecl<*>>, MutableSet<LitExpr<*>>>>()
  for (i in 0 until n) {
    val root = uf.find(i)
    val item = pointsTo[i]
    val group = groups.getOrPut(root) { mutableSetOf<VarDecl<*>>() to mutableSetOf() }
    group.first.add(item.first)
    group.second.addAll(item.second)
  }

  return groups.values.toList()
}

private class UnionFind(n: Int) {
  private val parent = IntArray(n) { it }
  private val rank = IntArray(n) { 0 }

  fun find(x: Int): Int {
    if (parent[x] != x) parent[x] = find(parent[x])
    return parent[x]
  }

  fun union(x: Int, y: Int) {
    val rootX = find(x)
    val rootY = find(y)
    if (rootX == rootY) return

    if (rank[rootX] < rank[rootY]) {
      parent[rootX] = rootY
    } else if (rank[rootX] > rank[rootY]) {
      parent[rootY] = rootX
    } else {
      parent[rootY] = rootX
      rank[rootX]++
    }
  }
}
