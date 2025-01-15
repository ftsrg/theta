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

import hu.bme.mit.theta.analysis.algorithm.oc.EventType.READ
import hu.bme.mit.theta.analysis.algorithm.oc.EventType.WRITE
import hu.bme.mit.theta.core.decl.VarDecl

internal fun interface MemoryConsistencyModelFilter {
  operator fun invoke(
    pos: List<R>,
    rfs: Map<VarDecl<*>, Set<R>>,
    wss: Map<VarDecl<*>, Set<R>>,
  ): Triple<List<R>, Map<VarDecl<*>, Set<R>>, Map<VarDecl<*>, Set<R>>>
}

@Suppress("unused")
enum class XcfaOcMemoryConsistencyModel(internal val filter: MemoryConsistencyModelFilter) {
  SC({ pos, rfs, wss -> Triple(pos, rfs, wss) }),
  WSC({ pos, rfs, _ -> Triple(pos, rfs, mapOf()) }),
  TSO({ pos, rfs, wss ->
    val newPos =
      pos.filter {
        !(it.from.const.varDecl != it.to.const.varDecl &&
          it.from.type == WRITE &&
          it.to.type == READ)
      }
    Triple(newPos, rfs, wss)
  }),
  PSO({ pos, rfs, wss ->
    val newPos =
      pos.filter { !(it.from.const.varDecl != it.to.const.varDecl && it.from.type == WRITE) }
    Triple(newPos, rfs, wss)
  }),
}
