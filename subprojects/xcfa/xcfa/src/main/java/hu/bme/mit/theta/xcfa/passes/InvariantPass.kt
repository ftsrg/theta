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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.clock.constr.ClockConstr
import hu.bme.mit.theta.core.clock.constr.FalseConstr
import hu.bme.mit.theta.core.clock.constr.TrueConstr
import hu.bme.mit.theta.core.clock.constr.UnitConstr
import hu.bme.mit.theta.core.clock.constr.UnitLeqConstr
import hu.bme.mit.theta.core.clock.constr.UnitLtConstr
import hu.bme.mit.theta.core.clock.op.GuardOp
import hu.bme.mit.theta.core.clock.op.ResetOp
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

class InvariantPass(val timed : Boolean) : ProcedurePass {

    private val edgesWithReset = HashSet<XcfaEdge>()
    private val edgeMinUpperBound = HashMap<XcfaEdge, ClockConstr>()

    private val upperBoundComparator = Comparator<ClockConstr> { constr1, constr2 ->
        when {
            constr1 is TrueConstr && constr2 is TrueConstr -> 0
            constr1 is TrueConstr -> 1 // constr1 is higher
            constr2 is TrueConstr -> -1 // constr2 is higher
            else -> when {
                constr1 is FalseConstr && constr2 is FalseConstr -> 0
                constr1 is FalseConstr -> -1 // constr2 is higher
                constr2 is FalseConstr -> 1 // constr1 is higher
                else -> {
                    constr1 as UnitConstr; constr2 as UnitConstr
                    when {
                        constr1.bound != constr2.bound -> constr1.bound.compareTo(constr2.bound)
                        constr1 is UnitLeqConstr && constr2 is UnitLtConstr -> 1 // constr1 is higher
                        constr1 is UnitLtConstr && constr2 is UnitLeqConstr -> -1 // constr1 is lower
                        else -> 0
                    }
                }
            }
        }
    }

    private fun XcfaEdge.getMinUpperBound(clock : VarDecl<RatType>) : ClockConstr =
        edgeMinUpperBound.computeIfAbsent(this, { edge ->
            // on a single edge, time can only elapse until the minimum upper bound on the edge
            var minBoundOnEdge : ClockConstr = TrueConstr()
            for (label in edge.getFlatLabels()) {
                if (label is ClockOpLabel) {
                    if (label.op is ResetOp && label.op.`var`.equals(clock)) {
                        edgesWithReset.add(edge)
                        break // bounds after a reset should not be considered
                    }
                    if (label.op is GuardOp && isUpperBound(label.op.constr)
                        && (label.op.constr as UnitConstr).`var`.equals(clock)) {
                        minBoundOnEdge = minOf(minBoundOnEdge, label.op.constr, upperBoundComparator)
                    }
                }
            }
            minBoundOnEdge
        })

    private fun isUpperBound(clockConstr : ClockConstr) = clockConstr is UnitLeqConstr || clockConstr is UnitLtConstr

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        if (timed) {
            val locations = builder.getLocs()
            val globalClocks = builder.parent.getClocks().map { cast(it.wrappedVar, Rat()) }
            val procClocks = builder.getClocks()
            for (clock in globalClocks + procClocks) {
                // restart with new clock
                edgesWithReset.clear()
                edgeMinUpperBound.clear()
                // first iteration: no intermediate nodes are allowed
                val invariant = arrayListOf(
                    locations.associateWith { location ->
                        if (location.outgoingEdges.isEmpty()) {
                            TrueConstr()
                        } else {
                            // different paths can be taken, time must be allowed to elapse until the maximum bound
                            var maxBoundedPath: ClockConstr = FalseConstr()
                            for (outEdge in location.outgoingEdges) {
                                maxBoundedPath = maxOf(maxBoundedPath, outEdge.getMinUpperBound(clock), upperBoundComparator)
                            }
                            maxBoundedPath.also { check(it !is FalseConstr) }
                        }
                    }
                )
                // i = # of intermediate nodes allowed
                for (i in 1 until locations.size) {
                    var changed = false
                    val preInvariant = invariant[i-1]
                    invariant.add(
                        locations.associateWith { location ->
                            if (location.outgoingEdges.isEmpty()) {
                                TrueConstr()
                            } else {
                                // different paths can be taken, time must be allowed to elapse until the maximum bound
                                var maxBoundedPath: ClockConstr = FalseConstr()
                                for (outEdge in location.outgoingEdges) {
                                    // on a path, time can only elapse until the minimum upper bound on the path
                                    val minBoundOnThisPath =
                                        // bounds after a reset should not be considered
                                        if (edgesWithReset.contains(outEdge))
                                            outEdge.getMinUpperBound(clock) // minimum bound on this edge until reset
                                        else
                                            minOf(
                                                outEdge.getMinUpperBound(clock), // minimum bound on this edge
                                                preInvariant[outEdge.target]!!, // minimum bound on path from target
                                                upperBoundComparator
                                            )
                                    maxBoundedPath = maxOf(maxBoundedPath, minBoundOnThisPath, upperBoundComparator)
                                }
                                if (maxBoundedPath != preInvariant[location]) { changed = true }
                                maxBoundedPath.also { check(it !is FalseConstr) }
                            }
                        }
                    )
                    if (!changed) {
                        break
                    }
                }
                for (location in locations) {
                    builder.addInvariant(location, invariant[invariant.size - 1][location]!!)
                }
            }
        }
        return builder
    }
}
