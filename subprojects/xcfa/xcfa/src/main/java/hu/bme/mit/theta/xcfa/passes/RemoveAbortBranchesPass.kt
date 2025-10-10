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
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

class RemoveAbortBranchesPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder
      .getLocs()
      .filter { l ->
        l.outgoingEdges.isEmpty() &&
          !l.initial &&
          !l.final &&
          !l.error &&
          l.incomingEdges.size == 1 &&
          l.incomingEdges.first().getFlatLabels().all { it is StmtLabel && it.stmt is AssumeStmt }
      }
      .forEach {
        val incomingEdge = it.incomingEdges.first()
        builder.removeEdge(incomingEdge)
        builder.removeLoc(it)
      }
    return builder
  }
}
