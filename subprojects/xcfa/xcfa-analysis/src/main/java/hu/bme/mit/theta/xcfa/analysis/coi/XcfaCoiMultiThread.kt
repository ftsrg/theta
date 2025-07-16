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
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.isWritten
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.pointsTo

class XcfaCoiMultiThread(xcfa: XCFA) : XcfaCoi(xcfa) {

  private val startThreads: MutableSet<XcfaEdge> = mutableSetOf()
  private val edgeToProcedure: MutableMap<XcfaEdge, XcfaProcedure> = mutableMapOf()
  private var XcfaEdge.procedure: XcfaProcedure
    get() = edgeToProcedure[this]!!
    set(value) {
      edgeToProcedure[this] = value
    }

  private val interProcessObservers: MutableMap<XcfaEdge, Set<XcfaEdge>> = mutableMapOf()

  data class ProcedureEntry(val procedure: XcfaProcedure, val scc: Int, val pid: Int)

  override val lts =
    object : LTS<S, A> {
      override fun getEnabledActionsFor(state: S): Collection<A> {
        val enabled = coreLts.getEnabledActionsFor(state)
        return lastPrec?.let { replaceIrrelevantActions(state, enabled, it) } ?: enabled
      }

      override fun <P : Prec> getEnabledActionsFor(
        state: S,
        explored: Collection<A>,
        prec: P,
      ): Collection<A> {
        if (lastPrec != prec) reinitialize(prec)
        val enabled = coreLts.getEnabledActionsFor(state, explored, prec)
        return replaceIrrelevantActions(state, enabled, prec)
      }

      private fun replaceIrrelevantActions(
        state: S,
        enabled: Collection<A>,
        prec: Prec,
      ): Collection<A> {
        val procedures =
          state.processes
            .map { (pid, pState) ->
              val loc = pState.locs.peek()
              val procedure = loc.incomingEdges.ifEmpty(loc::outgoingEdges).first().procedure
              ProcedureEntry(procedure, loc.scc, pid)
            }
            .toMutableList()

        do {
          var anyNew = false
          startThreads
            .filter { edge ->
              procedures.any { edge.procedure == it.procedure && it.scc >= edge.source.scc }
            }
            .forEach { edge ->
              edge.getFlatLabels().filterIsInstance<StartLabel>().forEach { startLabel ->
                val procedure = xcfa.procedures.find { it.name == startLabel.name }!!
                val procedureEntry = ProcedureEntry(procedure, procedure.initLoc.scc, -1)
                if (procedureEntry !in procedures) {
                  procedures.add(procedureEntry)
                  anyNew = true
                }
              }
            }
        } while (anyNew)
        val multipleProcedures = findDuplicates(procedures.map { it.procedure })

        return enabled.map { action ->
          if (!isObserved(action, procedures, multipleProcedures)) {
            replace(action, prec)
          } else {
            action.transFuncVersion = null
            action
          }
        }
      }

      private fun isObserved(
        action: A,
        procedures: MutableList<ProcedureEntry>,
        multipleProcedures: Set<XcfaProcedure>,
      ): Boolean {
        val toVisit =
          edgeToProcedure.keys
            .filter { it.source == action.edge.source && it.target == action.edge.target }
            .toMutableList()
        val visited = mutableSetOf<XcfaEdge>()

        while (toVisit.isNotEmpty()) {
          val visiting = toVisit.removeAt(0)
          if (isRealObserver(visiting)) return true

          visited.add(visiting)
          val toAdd =
            (directObservers[visiting] ?: emptySet()) union
              (interProcessObservers[visiting]?.filter { edge ->
                procedures.any {
                  it.procedure.name == edge.procedure.name &&
                    it.scc >= edge.source.scc &&
                    (it.procedure.name != visiting.procedure.name ||
                      it.procedure in multipleProcedures)
                } // the edge is still reachable
              } ?: emptySet())
          toVisit.addAll(toAdd.filter { it !in visited })
        }
        return false
      }

      fun findDuplicates(list: List<XcfaProcedure>): Set<XcfaProcedure> {
        val seen = mutableSetOf<String>()
        val duplicates = mutableSetOf<XcfaProcedure>()
        for (item in list) {
          if (!seen.add(item.name)) {
            duplicates.add(item)
          }
        }
        return duplicates
      }
    }

  fun reinitialize(prec: Prec) {
    directObservers.clear()
    interProcessObservers.clear()
    xcfa.procedures.forEach { procedure ->
      procedure.edges.forEach { edge ->
        edge.procedure = procedure
        if (edge.getFlatLabels().any { it is StartLabel }) startThreads.add(edge)
        findDirectObservers(edge, prec)
        findInterProcessObservers(edge, prec)
      }
    }
    lastPrec = prec
  }

  private fun findInterProcessObservers(edge: XcfaEdge, prec: Prec) {
    val precVars = prec.usedVars
    val writtenVars =
      edge.collectVarsWithAccessType().filter { it.value.isWritten && it.key in precVars }
    if (writtenVars.isEmpty()) return
    val writtenMemLocs = writtenVars.pointsTo(xcfa)

    xcfa.procedures.forEach { procedure ->
      procedure.edges.forEach {
        addEdgeIfObserved(edge, it, writtenVars, writtenMemLocs, precVars, interProcessObservers)
      }
    }
  }

  override fun addToRelation(
    source: XcfaEdge,
    target: XcfaEdge,
    relation: MutableMap<XcfaEdge, Set<XcfaEdge>>,
  ) {
    relation[source] = relation.getOrDefault(source, setOf()) + target
  }
}
