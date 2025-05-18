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

class EliminateSelfLoops : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    while (true) {
      val selfLoop =
        builder.getEdges().firstOrNull { xcfaEdge -> xcfaEdge.source === xcfaEdge.target }
      if (selfLoop != null) {
        builder.removeEdge(selfLoop)
        val source = selfLoop.source
        val target =
          XcfaLocation(
            source.name + "_selfloop_" + XcfaLocation.uniqueCounter(),
            metadata = source.metadata,
          )
        builder.addLoc(target)
        builder.addEdge(XcfaEdge(source, target, selfLoop.label, selfLoop.metadata))
        builder.addEdge(
          XcfaEdge(target, source, SequenceLabel(listOf(NopLabel)), selfLoop.metadata)
        )
      } else {
        break
      }
    }
    builder.metaData["noSelfLoops"] = Unit
    return builder
  }
}
