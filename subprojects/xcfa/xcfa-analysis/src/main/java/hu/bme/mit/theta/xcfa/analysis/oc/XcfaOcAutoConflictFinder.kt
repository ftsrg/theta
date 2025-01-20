/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
enum class AutoConflictFinderConfig(
  internal val conflictFinder: (Int) -> XcfaOcAutoConflictFinder,
) {

  NONE({ NoConflictFinder }),
  SIMPLE({ SimpleConflictFinder }),
  GENERIC({ GenericConflictFinder(it) }),
}

internal fun interface XcfaOcAutoConflictFinder {
  fun findConflicts(
    threads: Set<Thread>,
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    rfs: Map<VarDecl<*>, Set<R>>,
    logger: Logger,
  ): List<Reason>
}

internal val NoConflictFinder = XcfaOcAutoConflictFinder { _, _, _, _ -> emptyList() }

internal val SimpleConflictFinder = XcfaOcAutoConflictFinder { threads, events, rfs, logger ->
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
  conflicts
}

internal class GenericConflictFinder(private val bound: Int) : XcfaOcAutoConflictFinder {

  override fun findConflicts(
    threads: Set<Thread>,
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
    rfs: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
    logger: Logger,
  ): List<Reason> {
    val conflicts = mutableListOf<Reason>()
    val exactPo = XcfaExactPo(threads)
    val po = { from: E, to: E -> exactPo.isPo(from, to) }

    fun MutableSet<out Reason>.filterOutDirectConflicts() = removeIf {
      po(it.to, it.from).also { isPo ->
        if (isPo) conflicts.add(it)
      }
    }

    val initialNonTrivialEdges = rfs.values.flatMap { it.map { rf -> RelationReason(rf) } }.toMutableSet()
    initialNonTrivialEdges.filterOutDirectConflicts()

    val nonTrivialEdges: MutableList<Set<Reason>> = mutableListOf(initialNonTrivialEdges)
    val paths: MutableList<List<List<Reason>>> = mutableListOf(initialNonTrivialEdges.map { listOf(it) })
    val enabledWss = mutableSetOf<Pair<R, E>>()
    val enabledFrs = mutableSetOf<Pair<R, E>>()

    fun findPath(from: E, to: E): Reason? {
      if (from.clkId == to.clkId) {
        if (from.id < to.id) return PoReason
        return null
      }
      if (po(from, to)) return PoReason
      return paths.last().find { po(from, it.first().from) && po(it.last().to, to) }?.let { CombinedReason(it) }
    }

    for (i in 2..bound) {
      val conflictSize = conflicts.size
      val newNonTrivialEdges = mutableSetOf<Reason>()
      val newPaths = mutableListOf<List<Reason>>()

      // Derive new WS and FR edges
      rfs.forEach { (v, vRfs) ->
        val writes = events[v]?.flatMap { it.value }?.filter { it.type == EventType.WRITE } ?: listOf()
        vRfs.forEach { rf ->
          writes
            .filter { rf.from != it && rf.from.potentialSameMemory(it) }
            .forEach { w ->
              if ((rf to w) !in enabledWss) {
                findPath(w, rf.to)?.let { wRfTo ->
                  newNonTrivialEdges.add(WriteSerializationReason(rf, w, wRfTo))
                  enabledWss.add(rf to w)
                }
              }
              if ((rf to w) !in enabledFrs) {
                findPath(rf.from, w)?.let { rfFromW ->
                  newNonTrivialEdges.add(FromReadReason(rf, w, rfFromW))
                  enabledFrs.add(rf to w)
                }
              }
            }
        }
      }
      newNonTrivialEdges.filterOutDirectConflicts()

      // Find cycles or extend paths
      // (non-trivial edges found in the indexth iteration are used to extend paths from the size-index-1th iteration)
      nonTrivialEdges.forEachIndexed { index, edges ->
        edges.forEach { edge ->
          paths[paths.size - index - 1].forEach { path ->
            if (po(path.last().to, edge.from)) {
              if (po(edge.to, path.first().from)) {
                conflicts.add(CombinedReason(path + edge))
              } else {
                newPaths.add(path + edge)
              }
            }
          }
        }
      }

      nonTrivialEdges.add(newNonTrivialEdges)
      paths.add(newPaths)

      conflicts.removeIf { conflict ->
        val clkId = conflict.reasons.first().from.clkId
        conflict.reasons.all { it.from.clkId == clkId && it.to.clkId == clkId }
      }

      logger.writeln(Logger.Level.INFO, "Conflicts with $i non-trivial edges: ${conflicts.size - conflictSize}")
    }

    return conflicts
  }
}
