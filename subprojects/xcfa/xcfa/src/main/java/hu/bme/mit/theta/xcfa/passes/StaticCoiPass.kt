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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.dereferencesWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isRead
import hu.bme.mit.theta.xcfa.utils.isWritten

/**
 * Removes assignments and havocs whose value nothing relevant reads. A variable is relevant when a
 * label that is always kept (assumes, calls, memory writes, returns) reads it, or a kept assignment
 * reads it to compute a relevant variable. The analysis is flow-insensitive and covers all
 * procedures, so it keeps more than needed but never drops a value a check or a call may see.
 *
 * Passes run phase by phase over all procedures, so the relevant variables are computed once, when
 * the first procedure reaches this pass: every procedure is in the same phase then, and removing
 * labels that write only irrelevant variables does not change which variables are relevant.
 */
class StaticCoiPass(private val property: XcfaProperty? = null) : ProcedurePass {

  companion object {

    var enabled = false
  }

  private var relevantFor: XcfaBuilder? = null
  private var relevant: Set<VarDecl<*>> = emptySet()

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    // a race may involve accesses that no error location depends on
    if (!enabled || property?.inputProperty == ErrorDetection.DATA_RACE) return builder

    if (relevantFor !== builder.parent) {
      relevant = relevantVars(builder.parent)
      relevantFor = builder.parent
    }

    builder.getEdges().toSet().forEach { edge ->
      val labels = edge.getFlatLabels()
      val kept = labels.filter { !it.canBeSimplified || it.writtenVars().any { v -> v in relevant } }
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

  private fun XcfaLabel.writtenVars() =
    collectVarsWithAccessType().filter { it.value.isWritten }.keys

  private fun XcfaLabel.readVars() = collectVarsWithAccessType().filter { it.value.isRead }.keys

  private fun relevantVars(xcfa: XcfaBuilder): Set<VarDecl<*>> {
    val procedures = xcfa.getProcedures() + xcfa.getInitProcedures().map { it.first }
    val writers = mutableMapOf<VarDecl<*>, MutableList<XcfaLabel>>()
    val relevant = mutableSetOf<VarDecl<*>>()
    val toVisit = ArrayDeque<VarDecl<*>>()
    fun mark(vars: Collection<VarDecl<*>>) =
      vars.forEach { if (relevant.add(it)) toVisit.add(it) }
    procedures.forEach { procedure ->
      procedure.getEdges().forEach { edge ->
        edge.getFlatLabels().forEach { label ->
          if (label.canBeSimplified) {
            label.writtenVars().forEach { writers.getOrPut(it) { mutableListOf() }.add(label) }
          } else {
            mark(label.readVars())
          }
        }
      }
    }
    while (toVisit.isNotEmpty()) {
      writers[toVisit.removeFirst()]?.forEach { mark(it.readVars()) }
    }
    return relevant
  }
}
