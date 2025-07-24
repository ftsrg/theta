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

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/** Removes assume(false) statements and any consequently unreachable edges and locations. */
class AssumeFalseRemovalPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.getEdges().toSet().forEach { edge ->
      if (
        edge.getFlatLabels().any {
          it is StmtLabel && it.stmt is AssumeStmt && it.stmt.cond is FalseExpr
        }
      ) {
        builder.removeEdge(edge)
      }
    }

    val getUnreachable: () -> List<XcfaLocation> = {
      builder.getLocs().filter { it.incomingEdges.isEmpty() && !it.initial }
    }
    var unreachable = getUnreachable()
    while (unreachable.isNotEmpty()) {
      unreachable.forEach { loc ->
        loc.outgoingEdges.forEach { builder.removeEdge(it) }
        builder.removeLoc(loc)
      }
      unreachable = getUnreachable()
    }
    return builder
  }
}
