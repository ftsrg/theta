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
    Array<Array<Boolean>>, // ppo
    MutableMap<VarDecl<*>, MutableSet<R>>, // wss
  >
}

@Suppress("unused")
enum class XcfaOcMemoryConsistencyModel(internal val filter: MemoryConsistencyModelFilter) {
  SC({ events, pos, wss -> getClosedPo(pos, events) to wss }),
  WSC({ events, pos, _ -> getClosedPo(pos, events) to mutableMapOf() }),
  TSO({ events, pos, wss ->
    getPpo(events, pos) { v1, access1, v2, access2 ->
      v1 != v2 && access1 == setOf(WRITE) && access2 == setOf(READ)
    } to wss
  }),
  PSO({ events, pos, wss ->
    getPpo(events, pos) { v1, access1, v2, _ -> v1 != v2 && access1 == setOf(WRITE) } to wss
  }),
}

private fun getClosedPo(
  pos: MutableList<R>,
  events: Map<VarDecl<*>, Map<Int, List<E>>>,
): Array<Array<Boolean>> {
  val eventSize = events.values.sumOf { v -> v.values.sumOf { it.size } }
  val rels = Array(eventSize) { Array(eventSize) { false } }
  val globalPos = pos.filter { it.from.clkId != it.to.clkId }
  close(rels, globalPos.map { it.from.clkId to it.to.clkId }, false)
  return rels
}

private typealias VarAccessMetadata = MutableMap<VarDecl<*>, MutableSet<EventType>>

private fun getBlockVarAccessMetadata(
  events: Map<VarDecl<*>, Map<Int, List<E>>>
): Array<VarAccessMetadata> {
  val blockVarAccessMetadata = Array<VarAccessMetadata>(Event.clkIdSize) { mutableMapOf() }
  events.values.forEach { v ->
    v.values.forEach { evs ->
      evs.forEach { e ->
        blockVarAccessMetadata[e.clkId].getOrPut(e.const.varDecl) { mutableSetOf() }.add(e.type)
      }
    }
  }
  return blockVarAccessMetadata
}

private fun getPpo(
  events: Map<VarDecl<*>, Map<Int, List<E>>>,
  pos: MutableList<R>,
  filterOut: (VarDecl<*>, Set<EventType>, VarDecl<*>, Set<EventType>) -> Boolean,
): Array<Array<Boolean>> {
  val closedPos = getClosedPo(pos, events)
  val blockVarAccessMetadata = getBlockVarAccessMetadata(events)
  closedPos.forEachIndexed { i, other ->
    other.forEachIndexed { j, b ->
      val f = {
        blockVarAccessMetadata[i].all { (v1, access1) ->
          blockVarAccessMetadata[j].all { (v2, access2) -> filterOut(v1, access1, v2, access2) }
        }
      }
      if (b && f()) closedPos[i][j] = false
    }
  }
  return closedPos
}
