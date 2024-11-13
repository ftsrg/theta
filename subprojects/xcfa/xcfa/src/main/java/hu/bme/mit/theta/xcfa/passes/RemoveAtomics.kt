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

import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.FenceLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

class RemoveAtomics : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    for (xcfaEdge in LinkedHashSet(builder.getEdges())) {
      val labels = xcfaEdge.getFlatLabels()
      val (beginIndex, beginLabel) =
        labels
          .mapIndexed { i1, i2 -> Pair(i1, i2) }
          .firstOrNull {
            it.second is FenceLabel && (it.second as FenceLabel).labels.contains("ATOMIC_BEGIN")
          } ?: continue
      val (endIndex, endLabel) =
        labels
          .mapIndexed { i1, i2 -> Pair(i1, i2) }
          .lastOrNull {
            it.second is FenceLabel && (it.second as FenceLabel).labels.contains("ATOMIC_END")
          } ?: continue
      val newLabels =
        labels.subList(0, beginIndex) +
          labels.subList(beginIndex + 1, endIndex).filter {
            it !is FenceLabel || !it.labels.any { it.contains("ATOMIC_") }
          } +
          labels.subList(endIndex + 1, labels.size)
      builder.removeEdge(xcfaEdge)
      builder.addEdge(xcfaEdge.withLabel(SequenceLabel(newLabels)))
    }
    return builder
  }
}
