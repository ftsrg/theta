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

import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isRead
import hu.bme.mit.theta.xcfa.utils.isWritten

/** Transforms uninit vars into havocs whenever possible. */
class NoUninitVar : ProcedurePass {
  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val mayUninitVarsPerLoc = mutableMapOf(Pair(builder.initLoc, builder.getVars()))
    val waitlist = FifoWaitlist.create<XcfaLocation>()
    waitlist.add(builder.initLoc)
    val visited = mutableSetOf<XcfaLocation>()
    while (!waitlist.isEmpty) {
      val loc = waitlist.remove()
      for (outgoingEdge in loc.outgoingEdges.toSet()) {
        var uninitVars = mayUninitVarsPerLoc[loc]!!
        val newLabels = mutableListOf<XcfaLabel>()
        for (flatLabel in outgoingEdge.getFlatLabels()) {
          val varsWithAccessType = flatLabel.collectVarsWithAccessType()
          val reads = varsWithAccessType.filter { it.value.isRead }.keys
          val needHavoc = reads intersect uninitVars
          newLabels.addAll(needHavoc.map { StmtLabel(Havoc(it)) })
          newLabels.add(flatLabel)
          val writes = varsWithAccessType.filter { it.value.isWritten }.keys
          uninitVars = uninitVars - writes - needHavoc
        }
        mayUninitVarsPerLoc[outgoingEdge.target] =
          (mayUninitVarsPerLoc[outgoingEdge.target] ?: emptySet()) union uninitVars
        if (!visited.contains(outgoingEdge.target)) {
          waitlist.add(outgoingEdge.target)
          visited.add(outgoingEdge.target)
        }
        if (outgoingEdge.getFlatLabels() != newLabels) {
          builder.removeEdge(outgoingEdge)
          builder.addEdge(
            outgoingEdge.withLabel(SequenceLabel(newLabels, metadata = outgoingEdge.label.metadata))
          )
        }
      }
    }
    return builder
  }
}
