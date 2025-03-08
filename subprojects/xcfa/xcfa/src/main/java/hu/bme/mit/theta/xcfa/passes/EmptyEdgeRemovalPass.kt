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

import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.xcfa.model.*

/** Removes edges that only contain NopLabels (possibly nested) */
class EmptyEdgeRemovalPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    while (true) {
      builder.getEdges().filter { it.label.isSureStuck() }.forEach { builder.removeEdge(it) }

      val edge =
        builder.getEdges().find {
          it.label.isNop() &&
            !it.target.error &&
            !it.target.final &&
            !it.source.initial &&
            //!it.metadata.isSubstantial() &&
            ((it.source.outgoingEdges.size == 1 && !it.source.name.contains("__THETA_")) ||
              (it.target.incomingEdges.size == 1) && !it.target.name.contains("__THETA_"))
        } ?: return builder
      val collapseBefore = edge.source.outgoingEdges.size == 1
      builder.removeEdge(edge)
      if (collapseBefore) {
        val incomingEdges = edge.source.incomingEdges.toList()
        incomingEdges.forEach { builder.removeEdge(it) }
        incomingEdges.forEach {
          builder.addEdge(
            it.withTarget(edge.target).withMetadata(edge.metadata)
          )
        }
        builder.removeLoc(edge.source)
      } else {
        val outgoingEdges = edge.target.outgoingEdges.toList()
        outgoingEdges.forEach { builder.removeEdge(it) }
        outgoingEdges.forEach {
          builder.addEdge(
            it.withSource(edge.source).withMetadata(edge.metadata)
          )
        }
        builder.removeLoc(edge.target)
      }
    }
  }

  private fun XcfaLabel.isSureStuck(): Boolean =
    when (this) {
      is SequenceLabel -> labels.any { it.isSureStuck() }
      is NondetLabel -> labels.all { it.isSureStuck() }
      is StmtLabel -> stmt == Assume(False())
      else -> false
    }

  private fun XcfaLabel.isNop(): Boolean =
    when (this) {
      is NondetLabel -> labels.all { it.isNop() }
      is SequenceLabel -> labels.all { it.isNop() }
      is NopLabel -> true
      is StmtLabel -> stmt == Assume(True())
      else -> false
    }
}
