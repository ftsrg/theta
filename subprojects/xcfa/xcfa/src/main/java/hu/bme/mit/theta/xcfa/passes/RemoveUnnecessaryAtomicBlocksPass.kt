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

import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.isAtomicBegin
import hu.bme.mit.theta.xcfa.isAtomicEnd
import hu.bme.mit.theta.xcfa.model.*

class RemoveUnnecessaryAtomicBlocksPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.getEdges().toSet().forEach { edge ->
      val labelsToRemove = mutableListOf<XcfaLabel>()
      val atomicBegins = mutableListOf<XcfaLabel>()
      edge.getFlatLabels().forEach { label ->
        if (label.isAtomicBegin) {
          atomicBegins.add(label)
        } else if (label.isAtomicEnd && atomicBegins.isNotEmpty()) {
          labelsToRemove.add(atomicBegins.removeLast())
          labelsToRemove.add(label)
        }
      }
      if (labelsToRemove.isNotEmpty()) {
        val newLabel = edge.label.removeLabels(labelsToRemove)
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(newLabel))
      }
    }
    return builder
  }

  private fun XcfaLabel.removeLabels(labelsToRemove: Collection<XcfaLabel>): XcfaLabel = when (this) {
    in labelsToRemove -> NopLabel
    is SequenceLabel -> SequenceLabel(labels.map { it.removeLabels(labelsToRemove) }.filter { it !is NopLabel })
    is NondetLabel -> NondetLabel(labels.map { it.removeLabels(labelsToRemove) }.filter { it !is NopLabel }.toSet())
    else -> this
  }
}