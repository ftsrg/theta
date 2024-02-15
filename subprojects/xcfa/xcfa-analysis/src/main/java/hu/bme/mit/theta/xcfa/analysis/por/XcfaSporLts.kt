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
package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import java.util.function.Predicate
import kotlin.random.Random

/**
 * LTS with a POR (Partial Order Reduction) algorithm applied as a filter when returning enabled actions.
 * The algorithm is similar to the static source-set based POR algorithm described in the following paper:
 * Abdulla, P., Aronis, S., Jonsson, B., Sagonas, K. (2017):
 * Comparing source sets and persistent sets for partial order reduction
 *
 * @param xcfa the XCFA of the verified program
 */
open class XcfaSporLts(protected val xcfa: XCFA) : LTS<XcfaState<*>, XcfaAction> {

    companion object {

        var random: Random = Random.Default
    }

    protected var simpleXcfaLts = getXcfaLts()

    /* CACHE COLLECTIONS */

    /**
     * Shared objects (~global variables) used by a transition.
     */
    private val usedSharedObjects: MutableMap<XcfaEdge, Set<Decl<out Type>>> = mutableMapOf()

    /**
     * Shared objects (~global variables) that are used by the key transition or by transitions reachable from the
     * current state via a given transition.
     */
    private val influencedSharedObjects: MutableMap<XcfaEdge, Set<Decl<out Type>>> = mutableMapOf()

    /**
     * Backward transitions in the transition system (a transition of a loop).
     */
    protected val backwardTransitions: MutableSet<XcfaEdge> = mutableSetOf()

    init {
        collectBackwardTransitions()
    }

    /**
     * Returns the enabled actions in the ARG from the given state filtered with a POR algorithm.
     *
     * @param state the state whose enabled actions we would like to know
     * @return the enabled actions
     */
    override fun getEnabledActionsFor(state: XcfaState<*>): Set<XcfaAction> {
        // Collecting enabled actions
        val allEnabledActions = simpleXcfaLts.getEnabledActionsFor(state)

        // Calculating the source set starting from every (or some of the) enabled transition; the minimal source set is stored
        var minimalSourceSet = setOf<XcfaAction>()
        val sourceSetFirstActions = getSourceSetFirstActions(state, allEnabledActions)
        for (firstActions in sourceSetFirstActions) {
            val sourceSet = calculateSourceSet(allEnabledActions, firstActions)
            if (minimalSourceSet.isEmpty() || sourceSet.size < minimalSourceSet.size) {
                minimalSourceSet = sourceSet
            }
        }
        return minimalSourceSet
    }

    /**
     * Returns the possible starting actions of a source set.
     *
     * @param allEnabledActions the enabled actions in the present state
     * @return the possible starting actions of a source set
     */
    protected fun getSourceSetFirstActions(state: XcfaState<*>,
        allEnabledActions: Collection<XcfaAction>): Collection<Collection<XcfaAction>> {
        val enabledActionsByProcess = allEnabledActions.groupBy(XcfaAction::pid)
        val enabledProcesses = enabledActionsByProcess.keys.toList().shuffled(random)
        return enabledProcesses.map { pid ->
            val firstProcesses = mutableSetOf(pid)
            checkMutexBlocks(state, pid, firstProcesses, enabledActionsByProcess)
            firstProcesses.flatMap { enabledActionsByProcess[it] ?: emptyList() }
        }
    }

    /**
     * Checks whether a process is blocked by a mutex and if it is, it adds the process that blocks it to the set of
     * first processes.
     *
     * @param state the current state
     * @param pid the process whose blocking is to be checked
     * @param firstProcesses the set of first processes
     * @param enabledActionsByProcess the enabled actions grouped by processes
     * @return the set of first processes
     */
    private fun checkMutexBlocks(state: XcfaState<*>, pid: Int, firstProcesses: MutableSet<Int>,
        enabledActionsByProcess: Map<Int, List<XcfaAction>>) {
        val processState = checkNotNull(state.processes[pid])
        if (!processState.paramsInitialized) return
        val disabledOutEdges = processState.locs.peek().outgoingEdges.filter { edge ->
            enabledActionsByProcess[pid]?.none { action -> action.target == edge.target } ?: true
        }
        disabledOutEdges.forEach { edge ->
            edge.getFlatLabels().filterIsInstance<FenceLabel>().forEach { fence ->
                fence.labels.filter { it.startsWith("mutex_lock") }.forEach { lock ->
                    val mutex = lock.substringAfter('(').substringBefore(')')
                    state.mutexes[mutex]?.let { pid2 ->
                        if (pid2 !in firstProcesses) {
                            firstProcesses.add(pid2)
                            checkMutexBlocks(state, pid2, firstProcesses, enabledActionsByProcess)
                        }
                    }
                }
            }
        }
    }

    /**
     * Calculates a source set of enabled actions starting from a particular action.
     *
     * @param enabledActions the enabled actions in the present state
     * @param firstActions   the actions that will be added to the source set as the first actions
     * @return a source set of enabled actions
     */
    private fun calculateSourceSet(enabledActions: Collection<XcfaAction>,
        firstActions: Collection<XcfaAction>): Set<XcfaAction> {
        if (firstActions.any(::isBackwardAction)) {
            return enabledActions.toSet()
        }
        val sourceSet = firstActions.toMutableSet()
        val otherActions = (enabledActions.toMutableSet() subtract sourceSet).toMutableSet() // actions not in the source set
        var addedNewAction = true
        while (addedNewAction) {
            addedNewAction = false
            val actionsToRemove = mutableSetOf<XcfaAction>()
            for (action in otherActions) {
                // for every action that is not in the source set it is checked whether it should be added to the source set
                // (because it is dependent with an action already in the source set)
                if (sourceSet.any { areDependents(it, action) }) {
                    if (isBackwardAction(action)) {
                        return enabledActions.toSet() // see POR algorithm for the reason of removing backward transitions
                    }
                    sourceSet.add(action)
                    actionsToRemove.add(action)
                    addedNewAction = true
                }
            }
            actionsToRemove.forEach(otherActions::remove)
        }
        return sourceSet
    }

    /**
     * Determines whether an action is dependent with another one (based on the notions introduced for the POR
     * algorithm) already in the source set.
     *
     * @param sourceSetAction the action in the source set
     * @param action          the other action (not in the source set)
     * @return true, if the two actions are dependent in the context of source sets
     */
    private fun areDependents(sourceSetAction: XcfaAction, action: XcfaAction): Boolean {
        val usedBySourceSetAction = getCachedUsedSharedObjects(getEdgeOf(sourceSetAction))
        return isSameProcess(sourceSetAction, action) ||
            getInfluencedSharedObjects(getEdgeOf(action)).any { it in usedBySourceSetAction }
    }

    /**
     * Determines whether two actions are in the same process.
     *
     * @param action1 the first action
     * @param action2 the second action
     * @return true, if the two actions are in the same process
     */
    protected fun isSameProcess(action1: XcfaAction, action2: XcfaAction) = action1.pid == action2.pid

    /**
     * Returns the global variables that an edge uses (it is present in one of its labels).
     *
     * @param edge whose global variables are to be returned
     * @return the set of used global variables
     */
    private fun getDirectlyUsedSharedObjects(edge: XcfaEdge): Set<VarDecl<out Type>> {
        val globalVars = xcfa.vars.map(XcfaGlobalVar::wrappedVar)
        return edge.getFlatLabels().flatMap { label ->
            label.collectVars().filter { it in globalVars }
        }.toSet()
    }

    /**
     * Returns the global variables that an edge uses or if it is the start of an atomic block the global variables
     * that are used in the atomic block.
     *
     * @param edge whose global variables are to be returned
     * @return the set of directly or indirectly used global variables
     */
    private fun getUsedSharedObjects(edge: XcfaEdge): Set<Decl<out Type>> {
        val flatLabels = edge.getFlatLabels()
        val mutexes = flatLabels.filterIsInstance<FenceLabel>().flatMap { it.acquiredMutexes }.toMutableSet()
        return if (mutexes.isEmpty()) {
            getDirectlyUsedSharedObjects(edge)
        } else {
            getSharedObjectsWithBFS(edge) { it.mutexOperations(mutexes) }.toSet()
        }
    }

    /**
     * Same as [getUsedSharedObjects] with an additional cache layer.
     *
     * @param edge whose shared objects are to be returned
     * @return the set of directly or indirectly used shared objects
     */
    protected fun getCachedUsedSharedObjects(edge: XcfaEdge): Set<Decl<out Type>> {
        if (!usedSharedObjects.containsKey(edge)) {
            val vars = getUsedSharedObjects(edge)
            usedSharedObjects[edge] = vars
        }
        return usedSharedObjects[edge]!!
    }

    /**
     * Returns the shared objects (~global variables) used by the given transition or by transitions that are reachable
     * via the given transition ("influenced shared objects").
     *
     * @param edge whose successor transitions' shared objects are to be returned.
     * @return the set of influenced shared objects
     */
    protected fun getInfluencedSharedObjects(edge: XcfaEdge): Set<Decl<out Type>> {
        if (!influencedSharedObjects.containsKey(edge)) {
            influencedSharedObjects[edge] = getSharedObjectsWithBFS(edge) { true }
        }
        return influencedSharedObjects[edge]!!
    }

    /**
     * Returns shared objects (~global variables) encountered in a search starting from a given transition.
     *
     * @param startTransition the start point (transition) of the search
     * @param goFurther       the predicate that tells whether more transitions have to be explored through this
     * transition
     * @return the set of encountered shared objects
     */
    private fun getSharedObjectsWithBFS(startTransition: XcfaEdge,
        goFurther: Predicate<XcfaEdge>): Set<Decl<out Type>> {
        val vars = mutableSetOf<Decl<out Type>>()
        val exploredEdges = mutableListOf<XcfaEdge>()
        val edgesToExplore = mutableListOf<XcfaEdge>()
        edgesToExplore.add(startTransition)
        while (edgesToExplore.isNotEmpty()) {
            val exploring = edgesToExplore.removeFirst()
            vars.addAll(getDirectlyUsedSharedObjects(exploring))
            if (goFurther.test(exploring)) {
                val successiveEdges = getSuccessiveTransitions(exploring)
                for (newEdge in successiveEdges) {
                    if (newEdge !in exploredEdges) {
                        edgesToExplore.add(newEdge)
                    }
                }
            }
            exploredEdges.add(exploring)
        }
        return vars
    }

    /**
     * Returns the xcfa edge of the given action.
     *
     * @param action the action whose edge is to be returned
     * @return the edge of the action
     */
    protected open fun getEdgeOf(action: XcfaAction) = action.edge

    /**
     * Returns the outgoing edges of the target of the given edge.
     *
     * @param edge the edge whose target's outgoing edges are to be returned
     * @return the outgoing edges of the target of the edge
     */
    private fun getSuccessiveTransitions(edge: XcfaEdge): Set<XcfaEdge> {
        val outgoingEdges = edge.target.outgoingEdges.toMutableSet()
        val startThreads = edge.getFlatLabels().filterIsInstance<StartLabel>().toList()
        if (startThreads.isNotEmpty()) { // for start thread labels, the thread procedure must be explored, too!
            startThreads.forEach { startThread ->
                outgoingEdges.addAll(xcfa.procedures.first { it.name == startThread.name }.initLoc.outgoingEdges)
            }
        }
        return outgoingEdges
    }

    /**
     * Determines whether the given action is a backward action.
     *
     * @param action the action to be classified as backward action or non-backward action
     * @return true, if the action is a backward action
     */
    protected open fun isBackwardAction(action: XcfaAction): Boolean = backwardTransitions.contains(getEdgeOf(action))

    /**
     * Collects backward edges of the given XCFA.
     */
    private fun collectBackwardTransitions() {
        for (procedure in xcfa.procedures) {
            // DFS for every procedure of the XCFA to discover backward edges
            val visitedLocations = mutableSetOf<XcfaLocation>()
            val stack = Stack<XcfaLocation>()

            stack.push(procedure.initLoc) // start from the initial location of the procedure
            while (stack.isNotEmpty()) {
                val visiting = stack.pop()
                visitedLocations.add(visiting)
                for (outgoingEdge in visiting.outgoingEdges) {
                    val target = outgoingEdge.target
                    if (visitedLocations.contains(target)) { // backward edge
                        backwardTransitions.add(outgoingEdge)
                    } else {
                        stack.push(target)
                    }
                }
            }
        }
    }
}