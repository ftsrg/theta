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

import hu.bme.mit.theta.xcfa.model.*

class NoParallelEdgesPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    for (edge in LinkedHashSet(builder.getEdges())) {
      val otherEdges =
        builder.getEdges().filter {
          it.source == edge.source && it.target == edge.target && it != edge
        }
      for (otherEdge in otherEdges) {
        builder.removeEdge(otherEdge)
        val target =
          XcfaLocation(
            otherEdge.target.name + XcfaLocation.uniqueCounter(),
            metadata = otherEdge.target.metadata,
          )
        builder.addEdge(otherEdge.withTarget(target))
        builder.addEdge(XcfaEdge(target, otherEdge.target, NopLabel, otherEdge.metadata))
      }
    }
    return builder
  }
}
