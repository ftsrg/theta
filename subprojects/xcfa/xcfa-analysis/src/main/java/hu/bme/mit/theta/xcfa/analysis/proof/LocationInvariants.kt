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
package hu.bme.mit.theta.xcfa.analysis.proof

import hu.bme.mit.theta.analysis.algorithm.PartitionedInvariantProof
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.xcfa.model.XcfaLocation

/**
 * Invariants per location. A transition invariant relates the current state to any earlier state at
 * the same location.
 */
data class LocationInvariants(
  private val locationInvariants: Map<XcfaLocation, Collection<ExprState>>,
  val isTransitionInvariant: Boolean = false,
) : PartitionedInvariantProof<XcfaLocation> {

  constructor() : this(emptyMap())

  override fun getPartitions(): Map<XcfaLocation, Collection<ExprState>> = locationInvariants
}
