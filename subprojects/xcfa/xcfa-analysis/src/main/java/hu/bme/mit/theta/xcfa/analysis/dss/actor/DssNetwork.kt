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
package hu.bme.mit.theta.xcfa.analysis.dss.actor

import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph

/**
 * One block network of a run. Networks of one run share the observer and the verdict, but each
 * reaches SAFE by its own quiescence and fails on its own; block ids must be unique across them.
 */
class DssNetwork(val blockGraph: BlockGraph, val behaviorFor: (Block) -> DssBlockBehavior) {

  val blockIds: Set<String> = blockGraph.blocks.mapTo(linkedSetOf()) { it.id }
}

/** [result], and the index of the network it came from; null if from the coordinator. */
data class DssRun(val result: DssResult, val network: Int?)

/**
 * Builds the coordinator of a multi-network run: an actor with the observer's view of every network
 * that may also send messages to blocks (`DssMeetingActor`).
 */
typealias DssCoordinatorFactory = (DssConnection) -> DssWorker

internal const val COORDINATOR_ID = "__coordinator__"

internal fun checkUniqueBlockIds(networks: List<DssNetwork>) {
  val ids = networks.flatMap { it.blockIds }
  require(ids.size == ids.toSet().size) { "Block ids must be unique across DSS networks: $ids" }
}

/** The network whose block or quiescence check [sender] is, by [quiescenceIdOf]. */
internal fun networkOf(
  networks: List<DssNetwork>,
  sender: String?,
  quiescenceIdOf: (Int) -> String,
): Int? =
  networks.indices.firstOrNull { sender in networks[it].blockIds || sender == quiescenceIdOf(it) }
