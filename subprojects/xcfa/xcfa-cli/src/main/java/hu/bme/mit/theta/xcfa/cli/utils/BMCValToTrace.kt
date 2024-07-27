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
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.metadata.EmptyMetaData
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.reverseMapping
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.*

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

fun valToAction(xcfa: XCFA, val1: Valuation, val2: Valuation, locMap: Map<XcfaLocation, Int>): XcfaAction {
    val loc1 = val1.getLocation(locMap)
    val loc2 = val2.getLocation(locMap)
    return XcfaAction(
        pid = 0,
        edge = xcfa.procedures.flatMap { it.edges }.firstOrNull { edge ->
            edge.source == loc1 && edge.target == loc2
        } ?: XcfaEdge(loc1, loc2, EmptyMetaData, NopLabel(EmptyMetaData))
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