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
import hu.bme.mit.theta.core.clock.constr.UnitConstr
import hu.bme.mit.theta.core.clock.constr.UnitLeqConstr
import hu.bme.mit.theta.core.clock.constr.UnitLtConstr
import hu.bme.mit.theta.core.clock.op.GuardOp
import hu.bme.mit.theta.core.clock.op.ResetOp
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import java.util.LinkedList
import java.util.Queue

class InvariantPass(val timed : Boolean) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        if (timed) {
            val invariants: Map<XcfaLocation, ClockConstr> = collectInvariants(builder.getLocs())
            for ((loc, invariant) in invariants) {
                builder.addInvariant(loc, invariant)
            }
        }
        return builder
    }

    private fun collectInvariants(locations : Collection<XcfaLocation>) : Map<XcfaLocation, ClockConstr> {
        val invariants : HashMap<XcfaLocation, ClockConstr> = HashMap()
        for (location in locations) {
            val edges : Queue<XcfaEdge> = LinkedList(location.outgoingEdges)
            val visitedLocations : MutableCollection<XcfaLocation> = arrayListOf(location)
            val upperBounds : MutableCollection<ClockConstr> = arrayListOf()
            while (edges.isNotEmpty()) {
                val edge = edges.remove()
                var closed = false
                for (label in edge.getFlatLabels()) {
                    if (label is ClockOpLabel) {
                        if (label.op is ResetOp) {
                            break
                        }
                        if (label.op is GuardOp && isUpperBound(label.op.constr)) {
                            upperBounds.add(label.op.constr)
                            closed = true
                        }
                    }
                }
                if (!closed) {
                    val newSource = edge.target
                    if (!visitedLocations.contains(newSource)) {
                        edges.addAll(newSource.outgoingEdges)
                        visitedLocations.add(newSource)
                    }
                }
            }
            if (upperBounds.isNotEmpty()) {
                val invariant = maxUpperBound(upperBounds)
                invariants.put(location, invariant)
            }
        }
        return invariants
    }

    private fun isUpperBound(clockConstr : ClockConstr) : Boolean = clockConstr is UnitLeqConstr || clockConstr is UnitLtConstr

    private fun maxUpperBound(upperBounds : Collection<ClockConstr>) : ClockConstr {
        check(upperBounds.all { isUpperBound(it) })
        return upperBounds.map { it as UnitConstr }.maxWith { constr1, constr2 ->
            when {
                constr1.bound != constr2.bound -> constr1.bound.compareTo(constr2.bound)
                constr1 is UnitLeqConstr && constr2 is UnitLtConstr -> 1  // constr1 is higher
                else -> -1  // constr1 is lower
            }
        }
    }
}
