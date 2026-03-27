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

package hu.bme.mit.theta.xcfa.analysis.timed

import hu.bme.mit.theta.core.clock.constr.TrueConstr
import hu.bme.mit.theta.core.clock.op.ClockOps.Guard
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.foldVarLookup
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.passes.changeVars
import kotlin.collections.component1
import kotlin.collections.component2
import kotlin.collections.plus

fun getActiveClocks(s : XcfaState<*>) : Collection<VarDecl<RatType>> {
    val (threadLocalClocks, globalClocks) = s.xcfa?.let { xcfa ->
        xcfa.clocks
            .partition { it.threadLocal }
            .toList().map { it.map {
                cast(it.wrappedVar, Rat())
            } }
    } ?: listOf(emptyList(), emptyList())
    val procClocks = s.processes.flatMap { proc ->
        val lookup = proc.value.foldVarLookup()
        ((proc.value.procedure?.clocks ?: emptyList()) + threadLocalClocks)
            .map { it.changeVars(lookup) }
    }
    return globalClocks + procClocks
}

fun getInvariants(locsToLookups: Map<XcfaLocation, Map<VarDecl<*>, VarDecl<*>>>) : List<XcfaLabel> {
    return locsToLookups
        .mapKeys { (loc, _) -> loc.invariant }
        .filter { (invariant, _) -> invariant !is TrueConstr }
        .map { (invariant, lookup) -> ClockOpLabel(Guard(invariant)).changeVars(lookup) }
}
