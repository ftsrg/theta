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

package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.reverseMapping
import hu.bme.mit.theta.xcfa.model.*
import java.util.*

private fun Valuation.getStackDepth(): Int? {
    val map = toMap()
    val currDepth = map.keys.firstOrNull { it.name == "__curr_depth_" }
    if (currDepth != null) {
        // we have a depth counter
        val lit = map[currDepth] as IntLitExpr
        return lit.value.toInt()
    } else {
        return null
    }
}

private fun Valuation.getLocation(locMap: Map<XcfaLocation, Int>): XcfaLocation {
    val map = toMap()
    val currDepth = map.keys.firstOrNull { it.name == "__curr_depth_" }
    val value = if (currDepth != null) {
        // we have a depth counter
        val lit = map[currDepth] as IntLitExpr
        val stackDepth = lit.value.toInt()
        map.keys.firstOrNull() { it.name == "__loc_${stackDepth}_" }
    } else {
        map.keys.firstOrNull() { it.name == "__loc_" }
    }
    val lit = map[value] as? IntLitExpr ?: error("Location not in valuation.")
    return locMap.reverseMapping()[lit.value.toInt()] ?: error("Location not found.")
}

private fun Valuation.getCallsite(callsiteMap: Map<InvokeLabel, Int>): InvokeLabel {
    val map = toMap()
    val currDepth = map.keys.firstOrNull { it.name == "__curr_depth_" }
    if (currDepth == null) error("Cannot find variable `__curr_depth_`")
    val lit = map[currDepth] as IntLitExpr
    val stackDepth = lit.value.toInt()
    val proc = map.keys.firstOrNull() { it.name == "__proc_${stackDepth}_" }
    val idx = map[proc] as? IntLitExpr ?: error("Callsite not in valuation.")
    return callsiteMap.reverseMapping()[idx.value.toInt()] ?: error("Callsite not found.")
}

private fun InvokeLabel.getInputAssignments(xcfa: XCFA): XcfaLabel {
    val proc = xcfa.procedures.find { it.name == name } ?: error("Procedure not found: $name")
    val stms = proc.params.mapIndexed { index, (varDecl, dir) ->
        if (dir != ParamDirection.OUT) {
            StmtLabel(
                Assign(cast(varDecl, varDecl.type), cast(params[index], varDecl.type)),
                this.metadata
            )
        } else null
    }.filterNotNull()
    return SequenceLabel(stms, metadata)
}

private fun InvokeLabel.getOutputAssignments(xcfa: XCFA): XcfaLabel {
    val proc = xcfa.procedures.find { it.name == name } ?: error("Procedure not found: $name")
    val stms = proc.params.mapIndexed { index, (varDecl, dir) ->
        if (dir != ParamDirection.IN) {
            val param = params[index] as RefExpr<*>
            StmtLabel(
                Assign(cast(param.decl as VarDecl<*>, varDecl.type), cast(varDecl.ref, varDecl.type)),
                this.metadata
            )
        } else null
    }.filterNotNull()
    return SequenceLabel(stms, metadata)
}

fun valToAction(
    xcfa: XCFA, val1: Valuation, val2: Valuation, locMap: Map<XcfaLocation, Int>, callsiteMap: Map<InvokeLabel, Int>
): XcfaAction {
    val loc1 = val1.getLocation(locMap)
    val loc2 = val2.getLocation(locMap)
    val s1 = val1.getStackDepth() ?: -1
    val s2 = val2.getStackDepth() ?: -1
    return XcfaAction(
        pid = 0,
        edge = xcfa.procedures.flatMap { it.edges }.firstOrNull { edge ->
            edge.source == loc1 && edge.target == loc2
        } ?: if (s1 < s2) {
            val2.getCallsite(callsiteMap).getInputAssignments(xcfa).let { XcfaEdge(loc1, loc2, it.metadata, it) }
        } else {
            val1.getCallsite(callsiteMap).getOutputAssignments(xcfa).let { XcfaEdge(loc1, loc2, it.metadata, it) }
        }
    )
}

fun valToState(xcfa: XCFA, locMap: Map<XcfaLocation, Int>, val1: Valuation): XcfaState<PtrState<ExplState>> {
    val valMap = val1.toMap()
    return XcfaState(
        xcfa = xcfa,
        processes = mapOf(Pair(0, XcfaProcessState(
            locs = LinkedList(
                listOf(val1.getLocation(locMap))
            ),
            varLookup = LinkedList(),
        ))),
        PtrState(ExplState.of(
            ImmutableValuation.from(
                val1.toMap()
                    .filter { !it.key.name.startsWith("__loc_") && !it.key.name.startsWith("__temp_") }
                    .map { Pair(Var("_" + "_" + it.key.name, it.key.type), it.value) }.toMap()))),
        mutexes = emptyMap(),
        threadLookup = emptyMap(),
        bottom = false
    )
}