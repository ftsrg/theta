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
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.getInitLoops
import hu.bme.mit.theta.xcfa.utils.getNonConcurrentEdges
import hu.bme.mit.theta.xcfa.utils.isRead
import hu.bme.mit.theta.xcfa.utils.isWritten
import hu.bme.mit.theta.xcfa.utils.mergeIncomingValuations
import hu.bme.mit.theta.xcfa.utils.simplify

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
    val initEdges =
      LinkedHashSet(
        if (builder in builder.parent.getInitProcedures().map { it.first }) {
          getNonConcurrentEdges(builder.parent, true).first
        } else {
          emptySet()
        }
      )
    val initLoops = getInitLoops(builder.initLoc, initEdges)

    val valuations = LinkedHashMap<XcfaEdge, Valuation>()
    val constValuation = MutableValuation()
    val modifiedGlobalVars =
      builder.parent
        .getVars()
        .map { it.wrappedVar }
        .separateConstAndModifiedVars(builder.parent.getProcedures(), constValuation)

    builder.getVars().separateConstAndModifiedVars(setOf(builder), constValuation)

    lateinit var lastEdges: LinkedHashSet<XcfaEdge>
    do {
      lastEdges = edges

      val toVisit = builder.initLoc.outgoingEdges.toMutableList()
      val visited = mutableSetOf<XcfaEdge>()
      while (toVisit.isNotEmpty()) {
        val edge =
          toVisit.find { candidate -> candidate.source.incomingEdges.all { it in visited } }
            ?: toVisit.first()
        toVisit.remove(edge)
        visited.add(edge)
        val incomingValuations = mergeIncomingValuations(edge.source, valuations, initLoops)
        val localValuation = MutableValuation.copyOf(incomingValuations)
        localValuation.putAll(constValuation)

        val oldLabels = edge.getFlatLabels()
        val newLabels = oldLabels.map { it.simplify(localValuation, parseContext) }

        if (edge !in initEdges || newLabels.any { it is InvokeLabel || it is StartLabel }) {
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
            visited.add(newEdge)
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

  /**
   * Separates the variables in this collection. The constant variables are added to the given
   * valuation with their values. Modified variables are returned as a list.
   */
  private fun Collection<VarDecl<*>>.separateConstAndModifiedVars(
    accessingProcedures: Set<XcfaProcedureBuilder>,
    constValuation: MutableValuation,
  ): List<VarDecl<*>> {
    val writes = associateWith { 0 }.toMutableMap()
    val firstWrites = mutableMapOf<VarDecl<*>, XcfaEdge>()
    accessingProcedures.forEach { proc ->
      val toVisit = mutableListOf(proc.initLoc)
      val visited = mutableSetOf<XcfaLocation>()
      while (toVisit.isNotEmpty()) {
        val loc = toVisit.removeFirst()
        if (!visited.add(loc)) continue
        loc.outgoingEdges.forEach { edge ->
          edge.collectVarsWithAccessType().forEach { (v, access) ->
            if (v in writes) {
              if (
                access.isWritten ||
                  (access.isRead && accessingProcedures.size == 1 && writes[v] == 0)
              ) {
                writes[v] = writes[v]!! + 1
                firstWrites.putIfAbsent(v, edge)
              }
            }
          }
          toVisit.add(edge.target)
        }
      }
    }

    return filter { v ->
      if (writes[v]!! > 1) {
        return@filter true
      }
      firstWrites[v]?.let { firstWrite ->
        val valuation = MutableValuation()
        firstWrite.getFlatLabels().forEach { it.simplify(valuation, parseContext) }
        valuation.toMap()[v]?.let { constValuation.put(v, it) }
      }
      false
    }
  }
}
