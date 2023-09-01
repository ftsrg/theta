/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import java.util.stream.Collectors

class RemoveDeadEnds(val parseContext: ParseContext) : ProcedurePass {

    // TODO: thread start and procedure call should not be dead-end! Use-case: while(1) pthread_create(..);
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val nonDeadEndEdges: MutableSet<XcfaEdge> = LinkedHashSet()
        val reachableEdges: MutableSet<XcfaEdge> = LinkedHashSet()
        val errorLoc = builder.errorLoc
        errorLoc.ifPresent { xcfaLocation: XcfaLocation ->
            collectNonDeadEndEdges(xcfaLocation, nonDeadEndEdges)
        }
        val finalLoc = builder.finalLoc
        finalLoc.ifPresent { xcfaLocation: XcfaLocation ->
            collectNonDeadEndEdges(xcfaLocation, nonDeadEndEdges)
        }

        builder.getEdges().filter { it.getFlatLabels().any { it is InvokeLabel || it is StartLabel } }.forEach {
            nonDeadEndEdges.add(it)
            collectNonDeadEndEdges(it.source, nonDeadEndEdges)
        }

        filterReachableEdges(builder.initLoc, reachableEdges)
        val collect = builder.getEdges().stream().filter { xcfaEdge: XcfaEdge ->
            (!nonDeadEndEdges.contains(xcfaEdge)
                || !reachableEdges.contains(xcfaEdge))
        }.collect(Collectors.toSet())
        for (edge in collect) {
            builder.removeEdge(edge!!)
        }
        return builder
    }

    private fun filterReachableEdges(loc: XcfaLocation, reachableEdges: MutableSet<XcfaEdge>) {
        val outgoingEdges: MutableSet<XcfaEdge> = LinkedHashSet(loc.outgoingEdges)
        while (!outgoingEdges.isEmpty()) {
            val any = outgoingEdges.stream().findAny()
            val outgoingEdge = any.get()
            outgoingEdges.remove(outgoingEdge)
            if (!reachableEdges.contains(outgoingEdge)) {
                reachableEdges.add(outgoingEdge)
                outgoingEdges.addAll(outgoingEdge.target.outgoingEdges)
            }
        }
    }

    private fun collectNonDeadEndEdges(loc: XcfaLocation, nonDeadEndEdges: MutableSet<XcfaEdge>) {
        val incomingEdges: MutableSet<XcfaEdge> = LinkedHashSet(loc.incomingEdges)
        while (!incomingEdges.isEmpty()) {
            val any = incomingEdges.stream().findAny()
            val incomingEdge = any.get()
            incomingEdges.remove(incomingEdge)
            if (!nonDeadEndEdges.contains(incomingEdge)) {
                nonDeadEndEdges.add(incomingEdge)
                incomingEdges.addAll(incomingEdge.source.incomingEdges)
            }
        }
    }
}
