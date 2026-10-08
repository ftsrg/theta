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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.ParamDirection
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/**
 * Backward (strong) live-variable analysis over a procedure. Over-approximates: only a plain
 * assignment or havoc kills a variable, every other label just adds what it reads or writes, and an
 * assignment makes its operands live only if its target is.
 */
fun strongLiveVars(builder: XcfaProcedureBuilder): Map<XcfaLocation, Set<VarDecl<*>>> {
  val live = builder.getLocs().associateWith { mutableSetOf<VarDecl<*>>() }.toMutableMap()
  builder
    .getParams()
    .filter { it.second != ParamDirection.IN }
    .forEach { (v, _) -> builder.finalLoc.ifPresent { live[it]?.add(v) } }
  val worklist = ArrayDeque(builder.getEdges())
  val queued = worklist.toMutableSet()
  while (worklist.isNotEmpty()) {
    val edge = worklist.removeFirst()
    queued.remove(edge)
    var l: Set<VarDecl<*>> = live[edge.target] ?: continue
    for (label in edge.getFlatLabels().reversed()) {
      val stmt = (label as? StmtLabel)?.stmt
      l =
        when (stmt) {
          is AssignStmt<*> ->
            if (stmt.varDecl in l) l - stmt.varDecl + ExprUtils.getVars(stmt.expr) else l
          is HavocStmt<*> -> l - stmt.varDecl
          else -> l + label.collectVarsWithAccessType().keys
        }
    }
    val src = live.getOrPut(edge.source) { mutableSetOf() }
    if (src.addAll(l)) edge.source.incomingEdges.forEach { if (queued.add(it)) worklist.add(it) }
  }
  return live
}
