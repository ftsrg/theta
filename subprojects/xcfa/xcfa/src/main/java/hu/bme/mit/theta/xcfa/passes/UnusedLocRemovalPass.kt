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

import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/** Removes unused locations */
class UnusedLocRemovalPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val reachable = mutableSetOf(builder.initLoc)
    val stack = mutableListOf(builder.initLoc)
    while (stack.isNotEmpty()) {
      stack.removeLast().outgoingEdges.forEach {
        if (reachable.add(it.target)) stack.add(it.target)
      }
    }
    // Reachability from the entry, not merely "has no incoming edge": loop unrolling leaves behind
    // whole *cycles* of copies past the unroll bound, and every location in such a cycle has an
    // incoming edge from within the cycle, so a predecessor-count test keeps it alive forever. The
    // edges out of that dead cycle then land on live merge points, where the OC checker waits for
    // predecessors that can never execute and gives up on the task with "loops".
    builder.removeLocs { !it.final && !it.error && !it.initial && it !in reachable }
    return builder
  }
}
