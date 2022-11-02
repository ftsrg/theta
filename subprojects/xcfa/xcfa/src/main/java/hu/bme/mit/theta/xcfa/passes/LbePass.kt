/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

import com.google.common.base.Preconditions
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import java.util.function.Consumer

/**
 * This pass simplifies the XCFA by joining certain edges to single edges.
 *
 *
 * Definitions:
 *
 *  * Parallel edges: edges with the same source and target location
 *  * Snake: a graph component where the incoming and outgoing degree of every location is 1 (except at the ends)
 *  * Middle location: a location whose incoming degree is 1
 *
 */
class LbePass : ProcedurePass {
    /**
     * LBE modes.
     */
    enum class LBELevel {
        /**
         * The pass returns the builder without applying any changes.
         */
        NO_LBE,

        /**
         * Enables collapsing of sequential edges of a location where the number of incoming edges to the location is
         * exactly 1. A new edge is created for every outgoing edge of the location combined with the labels of the
         * incoming
         * edge. Parallel edges are not collapsed.
         */
        LBE_SEQ,

        /**
         * Enables collapsing of sequential and parallel edges too.
         */
        LBE_FULL
    }

    /**
     * Enables printing of the XCFA before and after the transformation process. For debugging...
     */
    private val ENABLE_PRINT_TO_DOT = false
    var builder: XcfaProcedureBuilder? = null

    /**
     * Steps of graph transformation:
     *
     *
     *  1. Remove outgoing edges of the error location
     *  1. Join parallel edges to single edges and collapse snakes (see Definitions at [LbePass])
     *  1. Collapse sequential edges of locations whose incoming degree is 1, join possibly created parallel edges and
     * edge-pairs described in step 2
     *
     */
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        if (level == LBELevel.NO_LBE || builder.errorLoc.isEmpty) return builder
        Preconditions.checkNotNull(builder.metaData["deterministic"])
        Preconditions.checkNotNull(builder.metaData["noSelfLoops"])
        this.builder = builder
        printToDot("--- BEFORE TRANSFORMATION ---")

        // Step 1
        Preconditions.checkState(builder.errorLoc.isPresent)
        builder.errorLoc.get().outgoingEdges.forEach(Consumer { toRemove: XcfaEdge? -> builder.removeEdge(toRemove!!) })

        // Step 2
        collapseParallelsAndSnakes(ArrayList(builder.getLocs()))

        // Step 3
        removeAllMiddleLocations()
        printToDot("--- AFTER TRANSFORMATION ---")
        if (level == LBELevel.LBE_SEQ || level == LBELevel.LBE_FULL) builder.metaData["seqLbe"] = Unit
        return builder
    }

    /**
     * Collapses parallel edges and snakes with a starting list of locations to check. Possibly created new parallel
     * edges and snakes are collapsed too.
     *
     * @param locationsToVisit The starting list of locations to check.
     * @return Returns the list of removed locations.
     */
    private fun collapseParallelsAndSnakes(locationsToVisit: MutableList<XcfaLocation>): List<XcfaLocation> {
        val removedLocations: MutableList<XcfaLocation> = LinkedList()
        while (!locationsToVisit.isEmpty()) {
            val visiting = locationsToVisit[0]

            // Join parallel edges starting from "visiting" location
            if (level == LBELevel.LBE_FULL) {
                collapseParallelEdges(visiting, locationsToVisit)
            }

            // Collapse "visiting" location if it is part of a snake
            collapsePartOfSnake(visiting, locationsToVisit, removedLocations)
            locationsToVisit.remove(visiting)
        }
        return removedLocations
    }

    /**
     * Removes locations whose incoming degree is 1. A new edge is created for every outgoing edge of the location
     * combined with the labels of the incoming edge as a sequence (the labels of the incoming edge will be the first in
     * the sequence).
     */
    private fun removeAllMiddleLocations() {
        val locationsToVisit: MutableList<XcfaLocation> = ArrayList(builder!!.getLocs())
        while (!locationsToVisit.isEmpty()) {
            val visiting = locationsToVisit[0]
            if (visiting.incomingEdges.size == 1 && visiting.outgoingEdges.size > 1) {
                val previousLocation = visiting.incomingEdges.stream().findAny().get().source
                removeMiddleLocation(visiting)
                val start: MutableList<XcfaLocation> = ArrayList()
                start.add(previousLocation)
                val locationsToRemove = collapseParallelsAndSnakes(start)
                locationsToRemove.forEach(Consumer { o: XcfaLocation -> locationsToVisit.remove(o) })
            }
            locationsToVisit.remove(visiting)
        }
    }

    /**
     * Collapses all parallel edges starting from a location.
     *
     * @param location         the location from where the parallel edges start that we want to remove
     * @param locationsToVisit Adds the targets of parallel edges to this list (new parallel edges and snakes
     * can appear in these locations)
     */
    private fun collapseParallelEdges(location: XcfaLocation, locationsToVisit: MutableList<XcfaLocation>) {
        val edgesByTarget = HashMap<XcfaLocation, MutableList<XcfaEdge>>()
        for (edge in location.outgoingEdges) {
            val edgesToTarget = edgesByTarget.getOrDefault(edge.target, ArrayList())
            edgesToTarget.add(edge)
            edgesByTarget[edge.target] = edgesToTarget
        }
        for (key in edgesByTarget.keys) {
            val edgesToTarget: List<XcfaEdge> = edgesByTarget[key]!!
            if (edgesToTarget.size <= 1) continue
            val source = edgesToTarget[0].source
            val target = edgesToTarget[0].target
            var nondetLabel = NondetLabel(LinkedHashSet())
            for (edge in edgesToTarget) {
                val oldLabels: MutableSet<XcfaLabel> = LinkedHashSet(nondetLabel.labels)
                oldLabels.addAll(getNonDetBranch(java.util.List.of(edge.label)))
                nondetLabel = NondetLabel(oldLabels)
                builder!!.removeEdge(edge)
            }
            builder!!.addEdge(XcfaEdge(source, target, nondetLabel))
            if (edgesToTarget.size >= 2 && !locationsToVisit.contains(key)) {
                locationsToVisit.add(key)
            }
        }
    }

    /**
     * Collapses the incoming and outgoing edges of a location whose incoming and outgoing degree is 1.
     *
     * @param location         The location to collapse
     * @param locationsToVisit The change list, the location that is the source of the incoming edge of the location is
     * added to this list
     * @param removedLocations The list of removed locations: the collapsed location is added to this list
     */
    private fun collapsePartOfSnake(location: XcfaLocation, locationsToVisit: MutableList<XcfaLocation>, removedLocations: MutableList<XcfaLocation>) {
        if (location.incomingEdges.size == 1 && location.outgoingEdges.size == 1) {
            val previousLocation = location.incomingEdges.stream().findAny().get().source
            removeMiddleLocation(location)
            removedLocations.add(location)
            if (!locationsToVisit.contains(previousLocation)) {
                locationsToVisit.add(previousLocation)
            }
        }
    }

    /**
     * Wraps edge labels to a [SequenceLabel] if the edge does not have
     * exactly one label. If the labels contain one [NondetLabel], the NondetLabel's
     * labels are returned to simplify the formula.
     *
     * @param edgeLabels the edge labels we would like to add to the NonDetLabel
     * @return the list of labels to add to the NonDetLabel
     */
    private fun getNonDetBranch(edgeLabels: List<XcfaLabel>): Collection<XcfaLabel> {
        if (edgeLabels.size == 1) {
            val first = edgeLabels.stream().findAny().get()
            return if (first is NondetLabel) {
                first.labels
            } else edgeLabels
        }
        val labels: MutableSet<XcfaLabel> = LinkedHashSet()
        labels.add(SequenceLabel(edgeLabels))
        return labels
    }

    /**
     * Removes a location whose incoming degree is 1. A new edge is created for every outgoing edge of the location
     * combined with the labels of the incoming edge as a sequence (the labels of the incoming edge will be the first in
     * the sequence).
     *
     * @param location The location to remove
     */
    private fun removeMiddleLocation(location: XcfaLocation) {
        if (location.incomingEdges.size != 1) return
        val inEdge = location.incomingEdges.stream().findAny().get()
        builder!!.removeEdge(inEdge)
        builder!!.removeLoc(location)
        val edgesToRemove = java.util.List.copyOf(location.outgoingEdges)
        for (outEdge in edgesToRemove) {
            builder!!.removeEdge(outEdge)
            val newLabel: MutableList<XcfaLabel> = ArrayList()
            newLabel.add(inEdge.label)
            newLabel.add(outEdge.label)
            builder!!.addEdge(XcfaEdge(inEdge.source, outEdge.target, SequenceLabel(newLabel)))
        }
    }

    /**
     * Prints the XCFA in dot format to standard output.
     *
     * @param title the printed XCFA will be marked with this label
     */
    private fun printToDot(title: String) {
        if (ENABLE_PRINT_TO_DOT) {
            println(title)
            println("digraph G {")
            //			System.out.println(builder.toDot(Set.of(), Set.of()));
            println("}")
        }
    }

    companion object {
        /**
         * The level of LBE that specifies which type of graph transformations to apply.
         */
        var level = LBELevel.NO_LBE
    }
}