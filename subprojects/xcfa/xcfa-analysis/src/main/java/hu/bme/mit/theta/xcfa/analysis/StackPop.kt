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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import kotlin.jvm.optionals.getOrNull

/**
 * Marks the edge that skips the rest of a stack-covered frame, see [XcfaArgAbstractor.closePop].
 */
data object StackPopMetaData : MetaData() {

  override fun combine(other: MetaData): MetaData = this

  override fun isSubstantial(): Boolean = false
}

/**
 * Leap to the end of the current procedure, havocing output variables and modified globals.
 * Returns:
 * - single havoc action in a list, if leap is possible
 * - empty list, if the current procedure has no final location, so there's nothing to havoc
 * - null, if leaping is not possible in the procedure because it starts threads or modifies the
 *   memory
 */
val XCFA.leapToReturn:
  (pid: Int, process: XcfaProcessState, nextCnt: Int) -> List<XcfaAction>? by LazyDelegate {
  val globals = this.globalVars.map { it.wrappedVar }.toSet()
  val names = this.procedures.map { it.name }.toSet()
  val labels = this.procedures.associate { p -> p.name to p.edges.flatMap { it.getAllLabels() } }
  val callees =
    labels.mapValues { (_, labels) ->
      labels.filterIsInstance<InvokeLabel>().map { it.name }.filter { it in names }.toSet()
    }
  val writtenGlobals =
    labels.mapValues { (_, labels) ->
      labels
        .flatMap { label -> label.collectVarsWithAccessType().filterValues { it.isWritten }.keys }
        .filterTo(mutableSetOf()) { it in globals }
    }
  val unskippable =
    labels
      .filterValues { labels ->
        labels.any { it is StartLabel || (it as? StmtLabel)?.stmt is MemoryAssignStmt<*, *, *> }
      }
      .keys
      .toMutableSet()
  do {
    var changed = false
    callees.forEach { (caller, called) ->
      called.forEach { callee ->
        changed = writtenGlobals.getValue(caller).addAll(writtenGlobals.getValue(callee)) || changed
        if (callee in unskippable) changed = unskippable.add(caller) || changed
      }
    }
  } while (changed)

  val procedureOf =
    this.procedures.flatMap { procedure -> procedure.locs.map { it to procedure } }.toMap()

  return@LazyDelegate leap@{ pid: Int, process: XcfaProcessState, nextCnt: Int ->
    val location = process.locs.peek()
    if (location.final) return@leap null
    val procedure = procedureOf[location] ?: return@leap null
    if (procedure.name in unskippable) return@leap null
    val finalLoc = procedure.finalLoc.getOrNull() ?: return@leap emptyList<XcfaAction>()
    val varLookup = process.varLookup.peek()
    val outputs =
      procedure.params
        .filter { it.second != ParamDirection.IN }
        .map { varLookup[it.first] ?: it.first }
    val havocs = (writtenGlobals.getValue(procedure.name) + outputs).map { StmtLabel(Havoc(it)) }
    val edge = XcfaEdge(location, finalLoc, SequenceLabel(havocs), StackPopMetaData)
    return@leap listOf(XcfaAction(pid, edge, nextCnt = nextCnt))
  }
}
