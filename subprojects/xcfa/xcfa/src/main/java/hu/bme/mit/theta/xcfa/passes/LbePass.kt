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

import com.google.common.base.Preconditions
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getAtomicBlockInnerLocations
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
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
class LbePass(val parseContext: ParseContext) : ProcedurePass {

    companion object {

        /**
         * The level of LBE that specifies which type of graph transformations to apply.
         */
        var level = LbeLevel.NO_LBE
    }

    /**
     * LBE modes.
     */
    enum class LbeLevel {

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
         * Currently, [NondetLabel] is not supported by the analysis so this mode cannot be used.
         */
        LBE_FULL
    }

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
     *  1. Collapse atomic blocks sequentially (with LBE_LOCAL as [LbeLevel] configuration)
     *  1. Join parallel edges to single edges and collapse snakes (see Definitions at [LbePass])
     *  1. Collapse sequential edges of locations whose incoming degree is 1, join possibly created parallel edges and
     * edge-pairs described in step 2
     *
     */
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        if (level == LbeLevel.NO_LBE || builder.errorLoc.isEmpty) return builder

        if (level == LbeLevel.LBE_SEQ || level == LbeLevel.LBE_FULL && parseContext.multiThreading) {
            level = LbeLevel.LBE_LOCAL
        }

        Preconditions.checkNotNull(builder.metaData["deterministic"])
        Preconditions.checkNotNull(builder.metaData["noSelfLoops"])
        this.builder = builder

        // Step 0
        builder.errorLoc.get().outgoingEdges.forEach(builder::removeEdge)

        // Step 1
        if (level == LbeLevel.LBE_LOCAL) {
            collapseAtomics()
        }

        // Step 2
        collapseParallelsAndSnakes(builder.getLocs().toList(), false)

        // Step 3
        //if (level != LbeLevel.LBE_LOCAL) {
        removeAllMiddleLocations(builder.getLocs().toList(), false)
        //}
        return builder
    }

    val isPostInlining: Boolean
        get() = true

    /**
     * Collapses atomic blocks sequentially.
     */
    private fun collapseAtomics() {
        atomicPhase = true
        val atomicBlockInnerLocations = getAtomicBlockInnerLocations(builder)
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
    private fun collapseParallelsAndSnakes(locationsToVisit: List<XcfaLocation>,
        strict: Boolean): List<XcfaLocation> {
        val editedLocationsToVisit = locationsToVisit.toMutableList()
        val removedLocations = mutableListOf<XcfaLocation>()
        while (editedLocationsToVisit.isNotEmpty()) {
            val visiting = editedLocationsToVisit.first()
            if (!strict || locationsToVisit.contains(visiting)) {
                // Join parallel edges starting from "visiting" location
                if (level == LbeLevel.LBE_FULL) {
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
        val editedLocationsToVisit = locationsToVisit.toMutableList()
        while (editedLocationsToVisit.isNotEmpty()) {
            val visiting = editedLocationsToVisit[0]
            if (!strict || locationsToVisit.contains(visiting)) {
                if (visiting.outgoingEdges.size == 1 && visiting.incomingEdges.size > 1) {
                    val nextLocation = visiting.outgoingEdges.first().target
                    val removed = removeMiddleLocation(visiting)
                    if (removed) {
                        val start = mutableListOf<XcfaLocation>()
                        start.add(nextLocation)
                        val locationsToRemove = collapseParallelsAndSnakes(start, strict)
                        locationsToRemove.forEach { editedLocationsToVisit.remove(it) }
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
    private fun collapseParallelEdges(location: XcfaLocation,
        locationsToVisit: MutableList<XcfaLocation>) {
        val edgesByTarget = mutableMapOf<XcfaLocation, MutableList<XcfaEdge>>()
        for (edge in location.outgoingEdges) {
            val edgesToTarget = edgesByTarget.getOrDefault(edge.target, ArrayList())
            edgesToTarget.add(edge)
            edgesByTarget[edge.target] = edgesToTarget
        }
        for (key in edgesByTarget.keys) {
            val edgesToTarget: List<XcfaEdge> = checkNotNull(edgesByTarget[key])
            if (edgesToTarget.size <= 1) continue
            val source = edgesToTarget[0].source
            val target = edgesToTarget[0].target
            var nondetLabel = NondetLabel(emptySet())
            for (edge in edgesToTarget) {
                val oldLabels = nondetLabel.labels.toMutableSet()
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
    private fun collapsePartOfSnake(location: XcfaLocation,
        locationsToVisit: MutableList<XcfaLocation>, removedLocations: MutableList<XcfaLocation>) {
        if (location.incomingEdges.size == 1 && location.outgoingEdges.size == 1) {
            val previousLocation = location.incomingEdges.first().source
            val removed = removeMiddleLocation(location)
            if (removed) removedLocations.add(location)
            if (previousLocation !in locationsToVisit) {
                locationsToVisit.add(previousLocation)
            }
        }
    }

    /**
     * Wraps edge labels to a [SequenceLabel] if the edge does not have
     * exactly one label. If the labels contain one [NondetLabel], the
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
        return setOf<XcfaLabel>(SequenceLabel(edgeLabels))
    }

    /**
     * Removes a location whose outgoing degree is 1. A new edge is created for every incoming edge of the location
     * combined with the labels of the outgoing edge as a sequence (the labels of the incoming edge will be the first in
     * the sequence).
     *
     * @param location The location to remove
     */
    private fun removeMiddleLocation(location: XcfaLocation): Boolean {
        if (location.outgoingEdges.size != 1) return false
        val outEdge = location.outgoingEdges.first()
        if (
            location.incomingEdges.any { edge -> edge.getFlatLabels().any { it is InvokeLabel } }
            || location.outgoingEdges.any { edge -> edge.getFlatLabels().any { it is InvokeLabel } }
            || (level == LbeLevel.LBE_LOCAL && !atomicPhase && isNotLocal(outEdge))
        ) {
            return false
        }

        builder.removeEdge(outEdge)
        builder.removeLoc(location)
        val edgesToRemove = location.incomingEdges.toSet()
        for (inEdge in edgesToRemove) {
            builder.removeEdge(inEdge)
            val newLabels = mutableListOf<XcfaLabel>()
            newLabels.addAll(inEdge.getFlatLabels())
            newLabels.addAll(outEdge.getFlatLabels())
            builder.addEdge(XcfaEdge(inEdge.source, outEdge.target, SequenceLabel(newLabels)))
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
        return !edge.getFlatLabels().all { label ->
            !(label is StartLabel || label is JoinLabel) && label.collectVars().all(builder.getVars()::contains) &&
                !(label is StmtLabel && label.stmt is AssumeStmt && label.stmt.cond is FalseExpr)
        }
    }
}