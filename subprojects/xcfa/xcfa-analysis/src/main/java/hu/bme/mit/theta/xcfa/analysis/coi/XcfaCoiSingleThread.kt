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
package hu.bme.mit.theta.xcfa.analysis.coi

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation

class XcfaCoiSingleThread(xcfa: XCFA) : XcfaCoi(xcfa) {

  private var observed: Set<Pair<XcfaLocation, XcfaLocation>> = setOf()

  override val lts =
    object : LTS<S, A> {
      override fun getEnabledActionsFor(state: S): Collection<A> {
        val enabled = coreLts.getEnabledActionsFor(state)
        return lastPrec?.let { replaceIrrelevantActions(enabled, it) } ?: enabled
      }

      override fun <P : Prec> getEnabledActionsFor(
        state: S,
        explored: Collection<A>,
        prec: P,
      ): Collection<A> {
        if (lastPrec != prec) reinitialize(prec)
        val enabled = coreLts.getEnabledActionsFor(state, explored, prec)
        return replaceIrrelevantActions(enabled, prec)
      }

      private fun replaceIrrelevantActions(enabled: Collection<A>, prec: Prec): Collection<A> =
        enabled.map { action ->
          if (Pair(action.source, action.target) !in observed) {
            replace(action, prec)
          } else {
            action.transFuncVersion = null
            action
          }
        }
    }

  fun reinitialize(prec: Prec) {
    lastPrec = prec
    directObservers.clear()
    val realObservers = mutableSetOf<XcfaEdge>()
    xcfa.procedures.forEach { procedure ->
      procedure.edges.forEach { edge ->
        findDirectObservers(edge, prec)
        if (isRealObserver(edge)) {
          realObservers.add(edge)
        }
      }
    }
    collectedObservedEdges(realObservers)
  }

  override fun addToRelation(
    source: XcfaEdge,
    target: XcfaEdge,
    relation: MutableMap<XcfaEdge, Set<XcfaEdge>>,
  ) {
    relation[target] = relation.getOrDefault(target, setOf()) + source
  }

  private fun collectedObservedEdges(realObservers: Set<XcfaEdge>) {
    val toVisit = realObservers.toMutableList()
    val visited = mutableSetOf<XcfaEdge>()
    while (toVisit.isNotEmpty()) {
      val visiting = toVisit.removeFirst()
      visited.add(visiting)
      val toAdd = directObservers[visiting] ?: emptySet()
      toVisit.addAll(toAdd.filter { it !in visited })
    }
    observed = visited.map { it.source to it.target }.toSet()
  }
}
