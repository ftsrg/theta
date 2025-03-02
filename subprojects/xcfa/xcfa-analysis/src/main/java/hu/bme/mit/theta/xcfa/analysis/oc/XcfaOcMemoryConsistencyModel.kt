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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.BooleanGlobalRelation
import hu.bme.mit.theta.analysis.algorithm.oc.Event
import hu.bme.mit.theta.analysis.algorithm.oc.EventType
import hu.bme.mit.theta.analysis.algorithm.oc.EventType.READ
import hu.bme.mit.theta.analysis.algorithm.oc.EventType.WRITE
import hu.bme.mit.theta.core.decl.VarDecl

internal fun interface MemoryConsistencyModelFilter {
  operator fun invoke(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: MutableList<R>,
    wss: MutableMap<VarDecl<*>, MutableSet<R>>,
  ): Pair<
    BooleanGlobalRelation, // ppo
    MutableMap<VarDecl<*>, MutableSet<R>>, // wss
  >
}

@Suppress("unused")
enum class XcfaOcMemoryConsistencyModel(internal val filter: MemoryConsistencyModelFilter) {
  SC({ _, pos, wss -> getClosedPo(pos) to wss }),
  WSC({ _, pos, _ -> getClosedPo(pos) to mutableMapOf() }),
  TSO({ events, pos, wss ->
    getPpo(events, pos) { v1, access1, v2, access2 ->
      v1 != v2 && access1 == setOf(WRITE) && access2 == setOf(READ)
    } to wss
  }),
  PSO({ events, pos, wss ->
    getPpo(events, pos) { v1, access1, v2, _ -> v1 != v2 && access1 == setOf(WRITE) } to wss
  }),
}

private fun getClosedPo(pos: MutableList<R>): BooleanGlobalRelation {
  val globalPos = pos.filter { it.from.clkId != it.to.clkId }
  val rels = BooleanGlobalRelation(Event.clkSize) { false }
  rels.closeNoCycle(globalPos.map { Triple(it.from.clkId, it.to.clkId, true) })
  return rels
}

private class BlockMetadata(
  val varAccess: MutableMap<VarDecl<*>, MutableSet<EventType>> = mutableMapOf(),
  var pid: Int? = null,
)

private fun getBlockMetadata(events: Map<VarDecl<*>, Map<Int, List<E>>>): Array<BlockMetadata> {
  val blockMetadata = Array(Event.clkSize) { BlockMetadata() }
  events.values.forEach { v ->
    v.values.forEach { evs ->
      evs.forEach { e ->
        val metadata = blockMetadata[e.clkId]
        metadata.varAccess.getOrPut(e.const.varDecl) { mutableSetOf() }.add(e.type)
        check(metadata.pid == null || metadata.pid == e.pid)
        metadata.pid = e.pid
      }
    }
  }
  return blockMetadata
}

private fun getPpo(
  events: Map<VarDecl<*>, Map<Int, List<E>>>,
  pos: MutableList<R>,
  filterOut: (VarDecl<*>, Set<EventType>, VarDecl<*>, Set<EventType>) -> Boolean,
): BooleanGlobalRelation {
  val closedPos = getClosedPo(pos)
  val blockMetadata = getBlockMetadata(events)
  fun ignore(i: Int, j: Int): Boolean {
    val metadata1 = blockMetadata[i]
    val metadata2 = blockMetadata[j]
    if (metadata1.pid != metadata2.pid) return false
    return metadata1.varAccess.all { (v1, access1) ->
      metadata2.varAccess.all { (v2, access2) -> filterOut(v1, access1, v2, access2) }
    }
  }
  closedPos.forEachPair { i, j, b -> if (b && ignore(i, j)) closedPos[i, j] = false }
  return closedPos
}
