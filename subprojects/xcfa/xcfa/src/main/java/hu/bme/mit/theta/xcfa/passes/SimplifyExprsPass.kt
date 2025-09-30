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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.getNonConcurrentEdges
import hu.bme.mit.theta.xcfa.isWritten
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.simplify
import java.util.Stack

/**
 * This pass simplifies the expressions inside statements and substitutes the values of constant
 * variables (that is, variables assigned only once). Requires the ProcedureBuilder to be
 * `deterministic` (@see DeterministicPass) Sets the `simplifiedExprs` flag on the ProcedureBuilder
 */
class SimplifyExprsPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    checkNotNull(builder.metaData["deterministic"])
    val unusedLocRemovalPass = UnusedLocRemovalPass()
    var edges = LinkedHashSet(builder.getEdges())
    val initEdges = LinkedHashSet(if (builder in builder.parent.getInitProcedures().map { it.first }) {
      getNonConcurrentEdges(builder.parent, true)
    } else {
      emptySet()
    })
    val initLoops = getInitLoops(builder.initLoc, initEdges)

    val valuations = LinkedHashMap<XcfaEdge, Valuation>()
    val constValuation = MutableValuation()
    val modifiedGlobalVars =
      builder.parent
        .getVars()
        .map { it.wrappedVar }
        .separateConstAndModifiedVariables(builder.parent.getProcedures(), constValuation)

    builder.getVars().separateConstAndModifiedVariables(setOf(builder), constValuation)

    lateinit var lastEdges: LinkedHashSet<XcfaEdge>
    do {
      lastEdges = edges

      val toVisit = builder.initLoc.outgoingEdges.toMutableList()
      val visited = mutableSetOf<XcfaEdge>()
      while (toVisit.isNotEmpty()) {
        val edge = toVisit.removeFirst()
        visited.add(edge)

        val nonModifiedValuation = if (edge.source.incomingEdges.size == 2 && edge.source in initLoops) {
          val loopEdges = initLoops[edge.source]!!
          val previousNonLoopEdge = edge.source.incomingEdges.first { it !in loopEdges }
          ImmutableValuation.from(valuations[previousNonLoopEdge]?.toMap()?.filter { (v, _) ->
            loopEdges.none { e -> e.collectVarsWithAccessType()[v]?.isWritten == true }
          })
        } else {
          null
        }
        val intersectedValuation =
          edge.source.incomingEdges
            .filter { it.getFlatLabels().none { l -> l is StmtLabel && l.stmt == Assume(False()) } }
            .map(valuations::get)
            .reduceOrNull(this::intersect)
        val incomingValuations = nonModifiedValuation union intersectedValuation
        val localValuation = MutableValuation.copyOf(incomingValuations)
        localValuation.putAll(constValuation)

        val oldLabels = edge.getFlatLabels()
        val newLabels = oldLabels.map { it.simplify(localValuation, parseContext) }

        if (edge !in initEdges) {
          // note that global variable values are still propagated within an edge (XcfaEdge is
          // considered atomic)
          modifiedGlobalVars.forEach { localValuation.remove(it) }
        }

        if (newLabels != oldLabels) {
          builder.removeEdge(edge)
          valuations.remove(edge)
          if (newLabels.firstOrNull().let { (it as? StmtLabel)?.stmt != Assume(False()) }) {
            val newEdge = edge.withLabel(SequenceLabel(newLabels))
            builder.addEdge(newEdge)
            valuations[newEdge] = localValuation
          }
        } else {
          valuations[edge] = localValuation
        }

        toVisit.addAll(edge.target.outgoingEdges.filter { it !in visited })
      }
      unusedLocRemovalPass.run(builder)

      edges = LinkedHashSet(builder.getEdges())
    } while (lastEdges != edges)
    builder.metaData["simplifiedExprs"] = Unit
    return builder
  }

  private fun intersect(v1: Valuation?, v2: Valuation?): Valuation {
    if (v1 == null || v2 == null) return ImmutableValuation.empty()
    val v1map = v1.toMap()
    val v2map = v2.toMap()
    return ImmutableValuation.from(
      v1map.filter { v2map.containsKey(it.key) && v2map[it.key] == it.value }
    )
  }

  private infix fun Valuation?.union(other: Valuation?): Valuation {
    val map1 = this?.toMap() ?: mapOf()
    val map2 = other?.toMap() ?: mapOf()
    return ImmutableValuation.from(map1 + map2)
  }

  /**
   * Separates the variables in this collection. The constant variables are added to the given
   * valuation with their values. Modified variables are returned as a list.
   */
  private fun Collection<VarDecl<*>>.separateConstAndModifiedVariables(
    acessingProcedures: Set<XcfaProcedureBuilder>,
    constValuation: MutableValuation,
  ): List<VarDecl<*>> = filter { v ->
    var firstWrite: XcfaEdge? = null
    (acessingProcedures.sumOf { p ->
        p.getEdges().count { e ->
          e.getFlatLabels()
            .any { l -> l.collectVarsWithAccessType().any { it.value.isWritten && it.key == v } }
            .also { written -> if (written && firstWrite == null) firstWrite = e }
        }
      } > 1)
      .also { modified ->
        if (!modified && firstWrite != null) {
          val valuation = MutableValuation()
          firstWrite!!.getFlatLabels().forEach { it.simplify(valuation, parseContext) }
          valuation.toMap()[v]?.let { constValuation.put(v, it) }
        }
      }
  }

  private fun getInitLoops(initLoc: XcfaLocation, initEdges: Set<XcfaEdge>): Map<XcfaLocation, Set<XcfaEdge>> {
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
}
