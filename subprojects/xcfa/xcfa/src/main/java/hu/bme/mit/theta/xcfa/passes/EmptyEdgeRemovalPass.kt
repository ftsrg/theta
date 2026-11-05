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

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.*
import java.util.IdentityHashMap

/** Removes edges that only contain NopLabels (possibly nested) */
class EmptyEdgeRemovalPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    // A collapse moves edges but keeps their label objects: no edge becomes stuck later, and the
    // costly simplification behind isNop is cached per label for the rescan after each collapse.
    builder.getEdges().filter { it.label.isSureStuck() }.forEach { builder.removeEdge(it) }
    val nop = IdentityHashMap<XcfaLabel, Boolean>()
    while (true) {
      val edge =
        builder.getEdges().find {
          nop.getOrPut(it.label) { it.label.isNop() } &&
            !it.metadata.isSubstantial() &&
            !it.target.error &&
            !it.target.final &&
            !it.source.initial &&
            ((it.source.outgoingEdges.size == 1 && !it.source.name.contains("__THETA_")) ||
              (it.target.incomingEdges.size == 1) && !it.target.name.contains("__THETA_"))
        } ?: return builder
      val collapseBefore = edge.source.outgoingEdges.size == 1
      builder.removeEdge(edge)
      if (collapseBefore) {
        val incomingEdges = edge.source.incomingEdges.toList()
        incomingEdges.forEach { builder.removeEdge(it) }
        incomingEdges.forEach {
          builder.addEdge(it.withTarget(edge.target).withMetadata(it.metadata))
        }
        builder.removeLoc(edge.source)
      } else {
        val outgoingEdges = edge.target.outgoingEdges.toList()
        outgoingEdges.forEach { builder.removeEdge(it) }
        outgoingEdges.forEach {
          builder.addEdge(it.withSource(edge.source).withMetadata(it.metadata))
        }
        builder.removeLoc(edge.target)
      }
    }
  }

  private fun XcfaLabel.isSureStuck(): Boolean =
    when (this) {
      is SequenceLabel -> labels.any { it.isSureStuck() }
      is NondetLabel -> labels.all { it.isSureStuck() }
      is StmtLabel -> (stmt as? AssumeStmt)?.cond?.let { ExprUtils.simplify(it) } == False()
      else -> false
    }

  private fun XcfaLabel.isNop(): Boolean =
    when (this) {
      is NondetLabel -> labels.all { it.isNop() }
      is SequenceLabel -> labels.all { it.isNop() }
      is NopLabel -> true
      is StmtLabel ->
        stmt == SkipStmt.getInstance() ||
          (stmt as? AssumeStmt)?.cond?.let { ExprUtils.simplify(it) } == True()
      else -> false
    }
}
