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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.model.*

class StaticCoiPass : ProcedurePass {

  companion object {

    var enabled = false
  }

  private val directObservers: MutableMap<XcfaLabel, Set<XcfaLabel>> = mutableMapOf()
  private val interProcessObservers: MutableMap<XcfaLabel, Set<XcfaLabel>> = mutableMapOf()
  private val interProcessVarObservers: MutableMap<VarDecl<*>, Set<XcfaLabel>> = mutableMapOf()

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!enabled) return builder

    builder.parent.getProcedures().forEach { procedure ->
      procedure.getEdges().forEach { edge ->
        val flatLabels = edge.getFlatLabels()
        flatLabels.forEachIndexed { index, label ->
          if (label is StmtLabel) {
            findDirectObservers(edge, label, flatLabels.subList(index + 1, flatLabels.size))
            findIndirectObservers(label, builder)
          }
        }
      }
    }

    builder.getEdges().toSet().forEach { edge ->
      val labels = edge.getFlatLabels()
      val kept = mutableListOf<XcfaLabel>()
      labels.forEach { label ->
        if (!label.canBeSimplified || isObserved(label)) {
          kept.add(label)
        }
      }
      if (kept.size != labels.size) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(kept, edge.label.metadata)))
      }
    }

    return builder
  }

  private val XcfaLabel.canBeSimplified
    get() =
      this is StmtLabel &&
        ((this.stmt is AssignStmt<*> && "_ret" !in this.stmt.varDecl.name) ||
          this.stmt is HavocStmt<*>) &&
        dereferencesWithAccessType.none { it.value.isWritten }

  private fun findDirectObservers(edge: XcfaEdge, label: XcfaLabel, remaining: List<XcfaLabel>) {
    val writtenVars =
      label.collectVarsWithAccessType().filter { it.value.isWritten }.map { it.key }.toSet()
    if (writtenVars.isEmpty()) return

    val toVisit = mutableListOf(edge)
    val visited = mutableSetOf<XcfaEdge>()
    while (toVisit.isNotEmpty()) {
      val visiting = toVisit.removeFirst()
      visited.add(visiting)
      val labels = if (visiting == edge) remaining else visiting.getFlatLabels()
      labels.forEach { target ->
        val vars = target.collectVarsWithAccessType()
        if (vars.any { it.key in writtenVars && it.value.isRead }) {
          directObservers[label] = directObservers.getOrDefault(label, setOf()) + target
        }
      }

      toVisit.addAll(visiting.target.outgoingEdges.filter { it !in visited })
    }
  }

  private fun findIndirectObservers(label: XcfaLabel, builder: XcfaProcedureBuilder) {
    val writtenVars =
      label.collectVarsWithAccessType().filter { it.value.isWritten }.map { it.key }.toSet()
    if (writtenVars.isEmpty()) return

    interProcessObservers[label] =
      writtenVars
        .flatMap { v ->
          interProcessVarObservers.getOrPut(v) {
            builder.parent
              .getProcedures()
              .flatMap { procedure ->
                procedure.getEdges().flatMap { e ->
                  e.getFlatLabels().filter { l ->
                    l.collectVarsWithAccessType().any { it.key == v && it.value.isRead }
                  }
                }
              }
              .toSet()
          }
        }
        .toSet()
  }

  private fun isObserved(label: XcfaLabel): Boolean {
    val toVisit = mutableListOf(label)
    val visited = mutableSetOf<XcfaLabel>()
    while (toVisit.isNotEmpty()) {
      val visiting = toVisit.removeFirst()
      if (visiting.collectAssumesVars().isNotEmpty()) return true
      if (visiting.dereferencesWithAccessType.any { it.value.isWritten }) return true

      visited.add(visiting)
      val toAdd =
        (directObservers[visiting] ?: emptySet()) union
          (interProcessObservers[visiting] ?: emptySet())
      toVisit.addAll(toAdd.filter { it !in visited })
    }
    return false
  }
}
