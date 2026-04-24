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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel

/** Transforms havocs into uninit vars whenever possible. */
class HavocToUninitVar : ProcedurePass {
  private var counter = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (builder.initLoc.incomingEdges.isNotEmpty()) {
      return builder
    }
    val nonLoopingEdges = getNonLoopingEdges(builder)
    for (edge in nonLoopingEdges) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (predicate((it.label as SequenceLabel).labels[0])) {
            val havocStmt = (it.label.labels[0] as StmtLabel).stmt as HavocStmt<*>
            val newVar =
              Var(havocStmt.varDecl.name + "__havoc_" + counter++, havocStmt.varDecl.type)
            builder.addVar(newVar)
            val assignStmt = AssignStmtLabel(havocStmt.varDecl, newVar.ref)
            builder.addEdge(
              XcfaEdge(it.source, it.target, SequenceLabel(listOf(assignStmt)), it.metadata)
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
    return builder
  }

  private fun predicate(it: XcfaLabel): Boolean {
    return it is StmtLabel && it.stmt is HavocStmt<*>
  }

  private fun getNonLoopingEdges(builder: XcfaProcedureBuilder): MutableList<XcfaEdge> {
    val initLoc = builder.initLoc

    val visited = mutableSetOf<XcfaEdge>()
    val inCurrentPath = mutableListOf<XcfaEdge>()
    val edgesInCycles = mutableSetOf<XcfaEdge>()

    // Depth-First Search to detect cycles and mark edges in cycles
    fun dfs(edge: XcfaEdge) {
      if (edge in inCurrentPath || edge in visited) {
        return
      }

      visited.add(edge)
      inCurrentPath.add(edge)

      for (outEdge in edge.target.outgoingEdges) {
        if (outEdge in inCurrentPath) {
          var i = inCurrentPath.indexOf(outEdge)
          while (i < inCurrentPath.size) {
            edgesInCycles.add(inCurrentPath[i])
            i++
          }
        }
        dfs(outEdge)
      }

      inCurrentPath.remove(edge)
    }

    // Start DFS from the initial location
    val dummyEdge = XcfaEdge(initLoc, initLoc, metadata = EmptyMetaData)
    dfs(dummyEdge)

    // Collect all edges not part of cycles
    val nonLoopingEdges = mutableListOf<XcfaEdge>()
    for (edge in visited) {
      if (edge !in edgesInCycles && edge != dummyEdge) {
        nonLoopingEdges.add(edge)
      }
    }
    return nonLoopingEdges
  }
}
