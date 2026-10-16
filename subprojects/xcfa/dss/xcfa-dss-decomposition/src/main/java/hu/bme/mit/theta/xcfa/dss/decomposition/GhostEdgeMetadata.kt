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

import hu.bme.mit.theta.xcfa.model.MetaData

/**
 * Marks a synthetic no-op edge/location inserted by [BlockGraphInstrumentation]. `XcfaLabel` is
 * sealed, so `NopLabel` is reused as the label (cf. CPAchecker's `GHOST_EDGE_DESCRIPTION`).
 */
object GhostEdgeMetadata : MetaData() {

  override fun combine(other: MetaData): MetaData = other

  override fun isSubstantial(): Boolean = false
}
