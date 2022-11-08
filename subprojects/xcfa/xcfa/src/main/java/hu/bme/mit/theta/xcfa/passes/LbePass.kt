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
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getAtomicBlockInnerLocations
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import java.util.function.Consumer
import kotlin.collections.set

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
         * Applies sequential collapsing on atomic blocks and consecutive local operations.
         */
        LBE_LOCAL,

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

    /**
     * Stores whether we are in the atomic collapsing phase.
     *
     * **Warning! Multiple parallel running of this pass instance does not work correctly!**
     */
    private var atomicPhase = false
    lateinit var builder: XcfaProcedureBuilder

    /**
     * Steps of graph transformation:
     *
     *
     *  1. Remove outgoing edges of the error location
     *  1. Collapse atomic blocks sequentially (with LBE_LOCAL as [LBELevel] configuration)
     *  1. Join parallel edges to single edges and collapse snakes (see Definitions at [SimpleLbePass])
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

        // Step 0
        builder.errorLoc.get().outgoingEdges.forEach(builder::removeEdge)

        // Step 1
        if (level == LBELevel.LBE_LOCAL) {
            collapseAtomics()
        }

        // Step 2
        collapseParallelsAndSnakes(ArrayList(builder.getLocs()), false)

        // Step 3
        if (level != LBELevel.LBE_LOCAL) {
            removeAllMiddleLocations(ArrayList(builder.getLocs()), false)
        }
        printToDot("--- AFTER TRANSFORMATION ---")
        return builder
    }

    val isPostInlining: Boolean
        get() = true

    /**
     * Collapses atomic blocks sequentially.
     */
    private fun collapseAtomics() {
        atomicPhase = true
        val atomicBlockInnerLocations: List<XcfaLocation> = getAtomicBlockInnerLocations(builder)
        collapseParallelsAndSnakes(atomicBlockInnerLocations, true)
        removeAllMiddleLocations(atomicBlockInnerLocations, true)
        atomicPhase = false
    }

    /**
     * Collapses parallel edges and snakes with a starting list of locations to check. Possibly created new parallel
     * edges and snakes are collapsed too.
     *
     * @param locationsToVisit The starting list of locations to check.
     * @param strict           If true, cascade collapsing is limited to locations in locationsToVisit.
     * @return Returns the list of removed locations.
     */
    private fun collapseParallelsAndSnakes(locationsToVisit: List<XcfaLocation>, strict: Boolean): List<XcfaLocation> {
        val editedLocationsToVisit: MutableList<XcfaLocation> = ArrayList(locationsToVisit)
        val removedLocations: MutableList<XcfaLocation> = LinkedList()
        while (!editedLocationsToVisit.isEmpty()) {
            val visiting = editedLocationsToVisit[0]
            if (!strict || locationsToVisit.contains(visiting)) {
                // Join parallel edges starting from "visiting" location
                if (level == LBELevel.LBE_FULL) {
                    collapseParallelEdges(visiting, editedLocationsToVisit)
                }

                // Collapse "visiting" location if it is part of a snake
                collapsePartOfSnake(visiting, editedLocationsToVisit, removedLocations)
            }
            editedLocationsToVisit.remove(visiting)
        }
        return removedLocations
    }

    /**
     * Removes locations whose incoming degree is 1. A new edge is created for every outgoing edge of the location
     * combined with the labels of the incoming edge as a sequence (the labels of the incoming edge will be the first in
     * the sequence).
     *
     * @param locationsToVisit The starting list of locations to check.
     * @param strict           If true, cascade collapsing is limited to locations in locationsToVisit.
     */
    private fun removeAllMiddleLocations(locationsToVisit: List<XcfaLocation>, strict: Boolean) {
        val editedLocationsToVisit: MutableList<XcfaLocation> = ArrayList(locationsToVisit)
        while (!editedLocationsToVisit.isEmpty()) {
            val visiting = editedLocationsToVisit[0]
            if (!strict || locationsToVisit.contains(visiting)) {
                if (visiting.incomingEdges.size == 1 && visiting.outgoingEdges.size > 1) {
                    val previousLocation: XcfaLocation = visiting.incomingEdges.first().source
                    val removed = removeMiddleLocation(visiting)
                    if (removed) {
                        val start: MutableList<XcfaLocation> = ArrayList()
                        start.add(previousLocation)
                        val locationsToRemove = collapseParallelsAndSnakes(start, strict)
                        locationsToRemove.forEach(Consumer { o: XcfaLocation -> editedLocationsToVisit.remove(o) })
                    }
                }
            }
            editedLocationsToVisit.remove(visiting)
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
            var nondetLabel = NondetLabel(emptySet())
            for (edge in edgesToTarget) {
                val oldLabels: MutableSet<XcfaLabel> = LinkedHashSet(nondetLabel.labels)
                oldLabels.addAll(getNonDetBranch(edge.getFlatLabels()))
                nondetLabel = NondetLabel(oldLabels)
                builder.removeEdge(edge)
            }
            builder.addEdge(XcfaEdge(source, target, nondetLabel))
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
            val previousLocation: XcfaLocation = location.incomingEdges.first().source
            val removed = removeMiddleLocation(location)
            if (removed) removedLocations.add(location)
            if (!locationsToVisit.contains(previousLocation)) {
                locationsToVisit.add(previousLocation)
            }
        }
    }

    /**
     * Wraps edge labels to a [hu.bme.mit.theta.xcfa.model.XcfaLabel.SequenceLabel] if the edge does not have
     * exactly one label. If the labels contain one [hu.bme.mit.theta.xcfa.model.XcfaLabel.NondetLabel], the
     * NondetLabel's labels are returned to simplify the formula.
     *
     * @param edgeLabels the edge labels we would like to add to the NonDetLabel
     * @return the list of labels to add to the NonDetLabel
     */
    private fun getNonDetBranch(edgeLabels: List<XcfaLabel>): Set<XcfaLabel> {
        if (edgeLabels.size == 1) {
            return if (edgeLabels[0] is NondetLabel) {
                (edgeLabels[0] as NondetLabel).labels
            } else edgeLabels.toSet()
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
    private fun removeMiddleLocation(location: XcfaLocation): Boolean {
        if (location.incomingEdges.size != 1) return false
        val inEdge: XcfaEdge = location.incomingEdges.first()
        if (level == LBELevel.LBE_LOCAL && !atomicPhase && location.outgoingEdges.stream().anyMatch { edge: XcfaEdge -> isNotLocal(edge) }) {
            return false
        }
        builder.removeEdge(inEdge)
        builder.removeLoc(location)
        val edgesToRemove = java.util.List.copyOf(location.outgoingEdges)
        for (outEdge in edgesToRemove) {
            builder.removeEdge(outEdge)
            val newLabel: MutableList<XcfaLabel> = ArrayList()
            newLabel.addAll(inEdge.getFlatLabels())
            newLabel.addAll(outEdge.getFlatLabels())
            builder.addEdge(XcfaEdge(inEdge.source, outEdge.target, SequenceLabel(newLabel)))
        }
        return true
    }

    /**
     * Determines whether an edge performs only local operations or not (thread start and join operations are not
     * considered local here).
     *
     * @param edge the edge whose "locality" is to be determined
     * @return true, if the edge performs at least one non-local operation
     */
    private fun isNotLocal(edge: XcfaEdge): Boolean {
        return !edge.getFlatLabels().stream().allMatch { label -> !(label is StartLabel || label is JoinLabel) && label.collectVars().toList().stream().allMatch(builder.getVars()::contains) }
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
            println("}")
            error("toDot not implemented on XcfaProcedureBuilder.")
        }
    }

    companion object {
        /**
         * The level of LBE that specifies which type of graph transformations to apply.
         */
        var level = LBELevel.NO_LBE
    }
}