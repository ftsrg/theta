/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import com.google.common.collect.Sets
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.isRead
import hu.bme.mit.theta.xcfa.model.*

/**
 * Remove unused variables from the program. Requires the ProcedureBuilder to be `deterministic`
 * (@see DeterministicPass)
 */
class UnusedVarPass(private val uniqueWarningLogger: Logger) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    checkNotNull(builder.metaData["deterministic"])

    val usedVars = LinkedHashSet<VarDecl<*>>()

    var edges = LinkedHashSet(builder.parent.getProcedures().flatMap { it.getEdges() })
    lateinit var lastEdges: Set<XcfaEdge>
    do {
      lastEdges = edges

      usedVars.clear()
      usedVars.addAll(
        builder.parent.getProcedures().flatMap {
          it.getParams().filter { it.second != ParamDirection.IN }.map { it.first }
        }
      )
      edges.forEach { edge ->
        usedVars.addAll(
          edge.label.collectVarsWithAccessType().filter { it.value.isRead }.map { it.key }
        )
      }

      builder.parent.getProcedures().forEach { b ->
        b.getEdges().toList().forEach { edge ->
          val newLabel = edge.label.removeUnusedWrites(usedVars)
          if (newLabel != edge.label) {
            b.removeEdge(edge)
            b.addEdge(edge.withLabel(newLabel))
          }
        }
      }

      edges = LinkedHashSet(builder.parent.getProcedures().flatMap { it.getEdges() })
    } while (lastEdges != edges)

    val allVars =
      Sets.union(
        builder.parent.getProcedures().flatMap { it.getVars() }.toSet(),
        builder.parent.getVars().map { it.wrappedVar }.toSet(),
      )
    val varsAndParams = Sets.union(allVars, builder.getParams().map { it.first }.toSet())
    if (!varsAndParams.containsAll(usedVars)) {
      uniqueWarningLogger.writeln(
        Logger.Level.INFO,
        "WARNING: There are some used variables not present as declarations: " +
          usedVars.filter { it !in varsAndParams },
      )
    }

    builder.getVars().filter { it !in usedVars }.forEach { builder.removeVar(it) }

    return builder
  }

  private fun XcfaLabel.removeUnusedWrites(usedVars: Set<VarDecl<*>>): XcfaLabel {
    return when (this) {
      is SequenceLabel ->
        SequenceLabel(labels.map { it.removeUnusedWrites(usedVars) }.filter { it !is NopLabel })

      is NondetLabel ->
        NondetLabel(
          labels.map { it.removeUnusedWrites(usedVars) }.filter { it !is NopLabel }.toSet()
        )

      is StmtLabel ->
        when (stmt) {
          is AssignStmt<*> -> if (stmt.varDecl in usedVars) this else NopLabel
          is HavocStmt<*> -> if (stmt.varDecl in usedVars) this else NopLabel
          else -> this
        }

      else -> this
    }
  }
}
