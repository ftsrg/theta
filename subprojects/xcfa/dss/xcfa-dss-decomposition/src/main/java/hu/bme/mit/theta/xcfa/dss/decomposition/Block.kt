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
package hu.bme.mit.theta.xcfa.dss.decomposition

import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation

/**
 * A coherent sub-graph of a procedure's CFG with one entry ([initialLocation]) and one exit
 * ([finalLocation]). Reuses the procedure's own locations/edges, so blocks can share boundaries.
 */
data class Block(
  val id: String,
  val initialLocation: XcfaLocation,
  val finalLocation: XcfaLocation,
  val locations: Set<XcfaLocation>,
  val edges: Set<XcfaEdge>,
  val predecessorIds: Set<String> = emptySet(),
  val successorIds: Set<String> = emptySet(),
  /**
   * Where a worker places this block's abstraction point, set by [BlockGraphInstrumentation].
   * Defaults to [finalLocation], i.e. no dedicated abstraction point (not instrumented yet).
   */
  val violationConditionLocation: XcfaLocation = finalLocation,
) {

  val isRoot: Boolean
    get() = predecessorIds.isEmpty()

  /** Whether this block has a dedicated abstraction point, distinct from [finalLocation]. */
  val isAbstractionPossible: Boolean
    get() = violationConditionLocation != finalLocation
}
