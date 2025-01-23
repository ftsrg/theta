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

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl

@Suppress("unused")
enum class AutoConflictFinderConfig {

  NONE,
  RF,
  RF_WS_FR,
}

internal fun findAutoConflicts(
  threads: Set<Thread>,
  events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
  rfs: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
  config: AutoConflictFinderConfig,
  logger: Logger,
): List<Reason> {
  if (config == AutoConflictFinderConfig.NONE) return emptyList()
  val exactPo = XcfaExactPo(threads)
  val po = { from: E, to: E -> exactPo.isPo(from, to) }
  val flatRfs = rfs.values.flatten().toMutableList()
  val conflicts = mutableListOf<Reason>()

  fun findSimplePath(from: E, to: E): Reason? {
    if (from.clkId == to.clkId) {
      if (from.id < to.id) return PoReason
      return null
    }
    if (po(from, to)) return PoReason
    return flatRfs.find { po(from, it.from) && po(it.to, to) }?.let { RelationReason(it) }
  }

  // Cycle of two RF edges (plus po edges)
  for (i in 0 until flatRfs.size) {
    for (j in i + 1 until flatRfs.size) {
      val rf1 = flatRfs[i]
      val rf2 = flatRfs[j]
      val clkId = rf1.from.clkId
      if (rf1.to.clkId == clkId && rf2.from.clkId == clkId && rf2.to.clkId == clkId) continue
      if (po(rf1.to, rf2.from) && po(rf2.to, rf1.from)) {
        conflicts.add(RelationReason(rf1) and RelationReason(rf2))
      }
    }
  }

  val rfCnt = conflicts.size
  logger.writeln(Logger.Level.INFO, "RF conflicts: $rfCnt")
  if (config == AutoConflictFinderConfig.RF) return conflicts

  // Find WS and FR conflicts
  rfs.forEach { (v, vRfs) ->
    val writes = events[v]?.flatMap { it.value }?.filter { it.type == EventType.WRITE } ?: listOf()
    vRfs.forEach { rf ->
      writes
        .filter { rf.from != it && rf.from.potentialSameMemory(it) }
        .forEach { w ->
          findSimplePath(w, rf.to)?.let { wRfTo ->
            findSimplePath(rf.from, w)?.let { rfFromW ->
              conflicts.add(WriteSerializationReason(rf, w, wRfTo) and rfFromW)
              conflicts.add(FromReadReason(rf, w, rfFromW) and wRfTo)
            }
          }
        }
    }
  }

  logger.writeln(Logger.Level.INFO, "WS, FR conflicts (2x): ${conflicts.size - rfCnt}")
  return conflicts
}
