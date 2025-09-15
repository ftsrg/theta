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
import hu.bme.mit.theta.core.clock.op.ClockOps
import hu.bme.mit.theta.core.clock.op.GuardOp
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import java.util.LinkedList
import java.util.Queue

class PropagateClockAssumptionsPass : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val invariants : Map<XcfaLocation, ClockConstr> = collectInvariants(builder.getLocs())
        for ((location, invariant) in invariants) {
            val invariantLabel = ClockOpLabel(ClockOps.Guard(invariant))
            for (incomingEdge in location.incomingEdges) {
                val newIncomingEdge = addLabelToEdge(incomingEdge, invariantLabel)
                builder.removeEdge(incomingEdge)
                builder.addEdge(newIncomingEdge)
            }
        }
        return builder
    }

    private fun collectInvariants(locations : Collection<XcfaLocation>) : Map<XcfaLocation, UnitConstr> {
        val invariants : HashMap<XcfaLocation, UnitConstr> = HashMap()
        for (location in locations) {
            val edges : Queue<XcfaEdge> = LinkedList(location.outgoingEdges)
            val visitedLocations : MutableCollection<XcfaLocation> = arrayListOf(location)
            val upperBounds : MutableCollection<UnitConstr> = arrayListOf()
            while (edges.isNotEmpty()) {
                val edge = edges.remove()
                var closed = false
                for (label in edge.getFlatLabels()) {
                    if (containsUpperBound(label)) {
                        upperBounds.add(extractUpperBound(label))
                        closed = true
                    }
                }
                if (!closed) {
                    val target = edge.target
                    if (!visitedLocations.contains(target)) {
                        edges.addAll(target.outgoingEdges)
                        visitedLocations.add(target)
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

    private fun containsUpperBound(label : XcfaLabel) : Boolean {
        return label is ClockOpLabel && label.op is GuardOp && isUpperBound(label.op.constr)
    }

    private fun extractUpperBound(label : XcfaLabel) : UnitConstr {
        return ((label as ClockOpLabel).op as GuardOp).constr as UnitConstr
    }

    private fun maxUpperBound(upperBounds : Collection<UnitConstr>) : UnitConstr {
        return upperBounds.maxWith { constr1, constr2 -> compareUpperBounds(constr1, constr2) }
    }

    private fun compareUpperBounds(constr1: UnitConstr, constr2: UnitConstr): Int {
        check(isUpperBound(constr1) && isUpperBound(constr2))
        return when {
            constr1.bound != constr2.bound -> constr1.bound.compareTo(constr2.bound)
            constr1 is UnitLeqConstr && constr2 is UnitLtConstr -> 1
            else -> -1
        }
    }
}
