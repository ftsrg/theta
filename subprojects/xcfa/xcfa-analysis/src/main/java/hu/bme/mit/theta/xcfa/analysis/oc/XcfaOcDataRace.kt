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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.BooleanGlobalRelation
import hu.bme.mit.theta.analysis.algorithm.oc.EventType.WRITE
import hu.bme.mit.theta.analysis.algorithm.oc.IOcChecker
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType

/** The conflicting access pairs of two atomic units, racing when the units are adjacent. */
internal class RaceCandidate(val pairs: List<Pair<E, E>>, adjacent: Expr<BoolType>) {

  fun pairCondition(e1: E, e2: E): Expr<BoolType> =
    listOfNotNull(e1.guardExpr, e2.guardExpr, e1.interferenceCond(e2)).toAnd()

  val condition: Expr<BoolType> = And(adjacent, Or(pairs.map { (e1, e2) -> pairCondition(e1, e2) }))
}

/**
 * Conflicting accesses of different threads, unordered by [ppos]: this also drops accesses in the
 * atomic unit of a thread start or join, which are adjacent to the other thread without racing.
 */
internal fun raceCandidates(
  eg: XcfaToEventGraph.EventGraph,
  ppos: BooleanGlobalRelation,
  checker: IOcChecker<E>,
): List<RaceCandidate> {
  val pairsByUnits = linkedMapOf<Pair<Int, Int>, MutableList<Pair<E, E>>>()
  for ((decl, byPid) in eg.events) {
    val accesses = byPid.mapValues { (_, events) -> events.filter { it.raceCandidate } }
    val pids = accesses.keys.sorted()
    for ((i, pid1) in pids.withIndex()) for (pid2 in pids.subList(i + 1, pids.size)) {
      for (e1 in accesses.getValue(pid1)) for (e2 in accesses.getValue(pid2)) {
        if (e1.type != WRITE && e2.type != WRITE) continue
        if (e1.inAtomicBlock && e2.inAtomicBlock) continue
        if (ppos[e1.clkId, e2.clkId] || ppos[e2.clkId, e1.clkId]) continue
        if (decl in eg.memoryDecls && !e1.potentialSameMemory(e2)) continue
        pairsByUnits.getOrPut(e1.clkId to e2.clkId) { mutableListOf() }.add(e1 to e2)
      }
    }
  }
  return pairsByUnits.values.map { pairs ->
    val (e1, e2) = pairs.first()
    RaceCandidate(pairs, checker.raceCondition(e1, e2))
  }
}
