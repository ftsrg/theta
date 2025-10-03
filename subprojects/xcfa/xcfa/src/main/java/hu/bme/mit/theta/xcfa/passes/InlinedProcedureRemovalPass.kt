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

import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/** Removes procedures that are not used anymore. */
class InlinedProcedureRemovalPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (builder in builder.parent.getInitProcedures().map { it.first }) return builder

    val isCalled =
      builder.parent.getProcedures().any { proc ->
        proc.getEdges().any { edge ->
          edge.getFlatLabels().any { label ->
            (label is InvokeLabel && label.name == builder.name) ||
              (label is StartLabel && label.name == builder.name)
          }
        }
      }
    if (!isCalled) {
      builder.parent.removeProcedure(builder)
    }
    return builder
  }
}
